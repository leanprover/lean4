// Lean compiler output
// Module: Lean.Elab.BuiltinTerm
// Imports: Init Lean.Elab.Open Lean.Elab.SetOption Lean.Elab.Eval
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
lean_object* l_Lean_Elab_Term_saveContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__4;
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__7;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit(lean_object*);
static lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetMVar___closed__5;
LEAN_EXPORT lean_object* l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___closed__2;
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__6;
lean_object* l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetMVar___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__4;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__6;
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_elabOpen___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__6;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetMVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__2;
static lean_object* l_Lean_Elab_Term_elabClear___lambda__2___closed__1;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__5;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabClear(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__2;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__32(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__3;
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__2;
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__4;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__2;
lean_object* l_Lean_toMessageList(lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetMVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__1;
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNumLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkTacticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__3;
static lean_object* l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabQuotedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2;
lean_object* l_Lean_Elab_Term_withInfoContext_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__5;
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__6;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Elab_Term_elabClear___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__3;
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__7;
lean_object* l_Lean_Elab_Term_registerMVarErrorHoleInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange(lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__24(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMap___at_Lean_resolveNamespace___spec__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__22(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__2;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabProp(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__4;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_elabOpen___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__7;
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2;
static lean_object* l_Lean_Elab_Term_elabDeclName___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange(lean_object*);
static lean_object* l_Lean_Elab_Term_elabProp___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__38(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__5;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNumLit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDoubleQuotedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__2;
static lean_object* l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__10;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__11;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNumLit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStrLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion(lean_object*);
lean_object* l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__2;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__22(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__4;
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__4;
static lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole___closed__5;
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Term_elabOpen___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__3;
extern lean_object* l_Lean_LocalContext_empty;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabNumLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHole(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange(lean_object*);
lean_object* l_Lean_Elab_Term_evalTerm___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar(lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__3;
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__1;
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear___closed__5;
lean_object* l_Lean_Elab_Term_mkSaveInfoAnnotation(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__3;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabByTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__7;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__2;
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPipeCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Term_elabOpen___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__4;
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Term_addDotCompletionInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__4;
static lean_object* l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkNoImplicitLambdaAnnotation(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__5;
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabByTactic___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__1;
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabQuotedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__2;
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__5;
lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__6;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPipeCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoImplicitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__23(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__7;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__3;
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__5;
lean_object* l_Array_sequenceMap___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__5;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__4;
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__5;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__14(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_elabOpen___spec__31(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__2;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__3;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear___closed__2;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__6;
static lean_object* l_Lean_Elab_Term_elabCharLit___closed__2;
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__36(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__1;
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange(lean_object*);
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__13(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_elabClear___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__3;
lean_object* l_Lean_Elab_Term_isTacticOrPostponedHole_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__3;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__3;
static lean_object* l_Lean_Elab_Term_elabIncludeStr___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__10;
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__7;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabCharLit___closed__3;
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__4;
lean_object* l_List_mapTR_loop___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__1;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabIncludeStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCharLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__7;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__3;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__3;
static lean_object* l_Lean_Elab_Term_elabOpen___closed__2;
extern lean_object* l_Lean_instInhabitedException;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__4;
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureTypeOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__1;
static lean_object* l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__7;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__5(size_t, size_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__5;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabOpen___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__5;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabIncludeStr___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole___closed__4;
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveLocalName_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__2;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__1;
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__15(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Term_elabOpen___spec__18(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabScientificLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addDotCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__4;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__7;
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__9;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole___closed__1;
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoImplicitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__3;
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__3;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__8;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabOpen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__7;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_elabOpen___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__3;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureTypeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabClear___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Term_elabOpen___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__35(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabCharLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange(lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange(lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabOpen___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCharLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole___closed__2;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__5;
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__25(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__8;
static lean_object* l_Lean_Elab_Term_elabIncludeStr___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__4;
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPipeCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName(lean_object*);
static lean_object* l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__1;
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__7;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__4;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__3;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__3;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__5;
static lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Term_elabOpen___spec__20(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__13;
static lean_object* l_Lean_Elab_Term_elabScientificLit___closed__5;
static lean_object* l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabByTactic___closed__3;
static lean_object* l_Lean_Elab_Term_elabNumLit___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__5;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__7;
extern lean_object* l_Lean_Expr_instBEqExpr;
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabByTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabClear___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSyntheticHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__5;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__1;
static lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__1;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__7;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabByTactic___closed__1;
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__7;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1;
lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__7;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabClear___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRawNatLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetMVar___closed__4;
static lean_object* l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabIncludeStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__2(size_t, size_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__5;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__21(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_scopedEnvExtensionsRef;
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDoubleQuotedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Elab_Term_elabClear___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetMVar___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__34(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__3;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__5;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfContainsMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_elabClear___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabOpen___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__5;
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__3;
static lean_object* l_Lean_Elab_Term_elabSetOption___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4;
static lean_object* l_Lean_Elab_Term_elabIncludeStr___closed__2;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__1;
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4;
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__1;
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__3;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__5;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRawNatLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__17___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__4;
static lean_object* l_Lean_Elab_Term_elabSyntheticHole___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__4;
lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabOpen___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__2;
uint8_t l_Lean_Expr_isSorry(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__5;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__1;
static lean_object* l_Lean_Elab_Term_elabNumLit___lambda__1___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNumLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__2;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__5;
lean_object* l_Lean_localDeclDependsOn___at_Lean_Elab_Term_addAutoBoundImplicits_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12___boxed(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkTacticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__1;
static lean_object* _init_l_Lean_Elab_Term_elabProp___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabProp___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabProp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("prop", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabProp", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabProp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__8;
x_5 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__10;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__2;
x_4 = lean_unsigned_to_nat(25u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__5;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabProp_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__8;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Syntax_isNone(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_Term_elabLevel(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_levelZero;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Expr_sort___override(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = l_Lean_Expr_sort___override(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabSort(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sort", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSort", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSort___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSort(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__2;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__5;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSort_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_elabOptLevel(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Level_succ___override(x_14);
x_16 = l_Lean_Expr_sort___override(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = l_Lean_Level_succ___override(x_17);
x_20 = l_Lean_Expr_sort___override(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabTypeStx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabTypeStx", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeStx___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__2;
x_4 = lean_unsigned_to_nat(53u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__5;
x_4 = lean_unsigned_to_nat(43u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid field notation, identifier or numeral expected", 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPipeCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2;
x_13 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPipeCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
x_13 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_elabTerm(x_11, x_12, x_13, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isSorry(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_addDotCompletionInfo(x_1, x_15, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabPipeCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pipeCompletion", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabPipeCompletion", 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPipeCompletion), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(34u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(38u);
x_2 = lean_unsigned_to_nat(78u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__2;
x_4 = lean_unsigned_to_nat(78u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(34u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(34u);
x_2 = lean_unsigned_to_nat(60u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__5;
x_4 = lean_unsigned_to_nat(60u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isIdent(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = l_Lean_Elab_Term_elabPipeCompletion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = l_Lean_Elab_Term_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_19 = l_Lean_Elab_Term_elabTerm(x_11, x_17, x_18, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_Lean_Elab_Term_addDotCompletionInfo(x_1, x_20, x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2;
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(x_25, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_25);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Elab_Term_SavedState_restore(x_15, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
x_33 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
lean_inc(x_1);
x_34 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_2);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_18);
x_35 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Term_addDotCompletionInfo___spec__1(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
lean_dec(x_1);
x_39 = l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2;
x_40 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_38);
return x_40;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("completion", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabCompletion", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCompletion), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(40u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(55u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__2;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(40u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(40u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__4;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__5;
x_4 = lean_unsigned_to_nat(52u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 8);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_5);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l_Lean_Expr_mvarId_x21(x_15);
x_18 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_17, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = 2;
x_24 = lean_box(0);
lean_inc(x_5);
x_25 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_mvarId_x21(x_26);
x_29 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_28, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_26);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = 0;
x_35 = lean_box(0);
lean_inc(x_5);
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_34, x_35, x_5, x_6, x_7, x_8, x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = l_Lean_Expr_mvarId_x21(x_37);
x_40 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_39, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_37);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabHole(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabHole", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHole___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(61u);
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__2;
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__5;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabHole_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_14, x_1);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 7);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_15, x_1);
x_17 = lean_box(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 7);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_21, x_1);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
static lean_object* _init_l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_LocalContext_contains(x_1, x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_st_ref_get(x_8, x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_6, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_14);
x_22 = l_Lean_MetavarContext_getDecl(x_21, x_14);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
lean_inc(x_1);
x_25 = l_Lean_LocalContext_isSubPrefixOf(x_23, x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_17);
x_26 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_2 = x_37;
x_9 = x_36;
goto _start;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec(x_1);
x_39 = 1;
x_40 = lean_box(x_39);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_14);
x_44 = l_Lean_MetavarContext_getDecl(x_43, x_14);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
lean_inc(x_1);
x_47 = l_Lean_LocalContext_isSubPrefixOf(x_45, x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = 0;
x_53 = lean_box(x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_2 = x_56;
x_9 = x_55;
goto _start;
}
}
else
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_14);
lean_dec(x_1);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_42);
return x_60;
}
}
}
case 5:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
x_63 = l_Lean_Expr_hasExprMVar(x_2);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Expr_hasFVar(x_2);
lean_dec(x_2);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_1);
x_65 = 1;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_9);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_inc(x_1);
x_68 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_62);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_2 = x_62;
x_9 = x_75;
goto _start;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_2);
lean_inc(x_1);
x_77 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_62);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_2 = x_62;
x_9 = x_84;
goto _start;
}
}
}
case 6:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_2, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
x_88 = l_Lean_Expr_hasExprMVar(x_2);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasFVar(x_2);
lean_dec(x_2);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_1);
x_90 = 1;
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_9);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_inc(x_1);
x_93 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
if (x_95 == 0)
{
uint8_t x_96; 
lean_dec(x_87);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_93, 0);
lean_dec(x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_94);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_2 = x_87;
x_9 = x_100;
goto _start;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_2);
lean_inc(x_1);
x_102 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
if (x_104 == 0)
{
uint8_t x_105; 
lean_dec(x_87);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_102, 0);
lean_dec(x_106);
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
lean_object* x_109; 
lean_dec(x_103);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_dec(x_102);
x_2 = x_87;
x_9 = x_109;
goto _start;
}
}
}
case 7:
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 2);
lean_inc(x_112);
x_113 = l_Lean_Expr_hasExprMVar(x_2);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = l_Lean_Expr_hasFVar(x_2);
lean_dec(x_2);
if (x_114 == 0)
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_1);
x_115 = 1;
x_116 = lean_box(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_9);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_inc(x_1);
x_118 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_112);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_118);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_118, 0);
lean_dec(x_122);
return x_118;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
else
{
lean_object* x_125; 
lean_dec(x_119);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_dec(x_118);
x_2 = x_112;
x_9 = x_125;
goto _start;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_2);
lean_inc(x_1);
x_127 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
if (x_129 == 0)
{
uint8_t x_130; 
lean_dec(x_112);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_127);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_127, 0);
lean_dec(x_131);
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
else
{
lean_object* x_134; 
lean_dec(x_128);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
lean_dec(x_127);
x_2 = x_112;
x_9 = x_134;
goto _start;
}
}
}
case 8:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 3);
lean_inc(x_138);
x_139 = l_Lean_Expr_hasExprMVar(x_2);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = l_Lean_Expr_hasFVar(x_2);
lean_dec(x_2);
if (x_140 == 0)
{
uint8_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_1);
x_141 = 1;
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_9);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_inc(x_1);
x_144 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_144);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_144, 0);
lean_dec(x_148);
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
lean_dec(x_144);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_145);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
lean_dec(x_144);
lean_inc(x_1);
x_152 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_unbox(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
lean_dec(x_138);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_152);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_152, 0);
lean_dec(x_156);
return x_152;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_dec(x_152);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_object* x_159; 
lean_dec(x_153);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_dec(x_152);
x_2 = x_138;
x_9 = x_159;
goto _start;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_2);
lean_inc(x_1);
x_161 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
if (x_163 == 0)
{
uint8_t x_164; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_161, 0);
lean_dec(x_165);
return x_161;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_dec(x_161);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_dec(x_162);
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
lean_dec(x_161);
lean_inc(x_1);
x_169 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
if (x_171 == 0)
{
uint8_t x_172; 
lean_dec(x_138);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_169);
if (x_172 == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_169, 0);
lean_dec(x_173);
return x_169;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_dec(x_169);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec(x_170);
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
lean_dec(x_169);
x_2 = x_138;
x_9 = x_176;
goto _start;
}
}
}
}
case 10:
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_2, 1);
lean_inc(x_178);
lean_dec(x_2);
x_2 = x_178;
goto _start;
}
case 11:
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_2, 2);
lean_inc(x_180);
lean_dec(x_2);
x_2 = x_180;
goto _start;
}
default: 
{
uint8_t x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_2);
lean_dec(x_1);
x_182 = 1;
x_183 = lean_box(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_9);
return x_184;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_3, x_4, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_1, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg), 10, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthetic hole has already been defined with an incompatible local context", 74);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSyntheticHole___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthetic hole has already beend defined and delayed assigned with an incompatible local context", 96);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSyntheticHole___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthetic hole has already been defined and assigned to value incompatible with the current context", 99);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSyntheticHole___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSyntheticHole___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSyntheticHole___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSyntheticHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_unsigned_to_nat(1u);
x_170 = l_Lean_Syntax_getArg(x_1, x_169);
x_171 = l_Lean_Syntax_isIdent(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_170);
x_172 = lean_box(0);
x_10 = x_172;
goto block_168;
}
else
{
lean_object* x_173; 
x_173 = l_Lean_Syntax_getId(x_170);
lean_dec(x_170);
x_10 = x_173;
goto block_168;
}
block_168:
{
uint8_t x_11; 
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_10);
x_19 = l_Lean_MetavarContext_findUserName_x3f(x_18, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = 2;
lean_inc(x_5);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_20, x_10, x_5, x_6, x_7, x_8, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_Expr_mvarId_x21(x_22);
x_25 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_24, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
lean_inc(x_30);
x_31 = l_Lean_Expr_mvar___override(x_30);
lean_inc(x_30);
x_32 = l_Lean_Elab_Term_getMVarDecl(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
lean_inc(x_36);
lean_inc(x_37);
x_39 = l_Lean_LocalContext_isSubPrefixOf(x_37, x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_32);
lean_dec(x_31);
lean_inc(x_30);
x_40 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_30);
x_43 = l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_LocalContext_isSubPrefixOf(x_36, x_37, x_38);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_Lean_Elab_Term_elabSyntheticHole___closed__2;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_49;
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = 2;
lean_inc(x_5);
x_51 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_50, x_10, x_5, x_6, x_7, x_8, x_46);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = l_Lean_Expr_mvarId_x21(x_52);
x_55 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_54, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_52);
x_57 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_30, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_52);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec(x_43);
x_63 = l_Lean_Elab_Term_elabSyntheticHole___closed__4;
x_64 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_ctor_get(x_41, 0);
lean_inc(x_66);
lean_dec(x_41);
x_67 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_68);
x_70 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_36, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_ctor_get(x_34, 4);
lean_inc(x_74);
lean_dec(x_34);
x_75 = l_Lean_indentExpr(x_68);
x_76 = l_Lean_Elab_Term_elabSyntheticHole___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1___boxed), 8, 1);
lean_closure_set(x_80, 0, x_79);
x_81 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(x_37, x_74, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_70);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_70, 0);
lean_dec(x_83);
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
lean_dec(x_70);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_32, 0);
x_87 = lean_ctor_get(x_32, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_32);
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
x_90 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
lean_inc(x_88);
lean_inc(x_89);
x_91 = l_Lean_LocalContext_isSubPrefixOf(x_89, x_88, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_31);
lean_inc(x_30);
x_92 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_87);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_86);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_30);
x_95 = l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l_Lean_LocalContext_isSubPrefixOf(x_88, x_89, x_90);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l_Lean_Elab_Term_elabSyntheticHole___closed__2;
x_101 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_98);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_101;
}
else
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = 2;
lean_inc(x_5);
x_103 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_102, x_10, x_5, x_6, x_7, x_8, x_98);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_104);
x_106 = l_Lean_Expr_mvarId_x21(x_104);
x_107 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_106, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_104);
x_109 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_30, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_104);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_95, 1);
lean_inc(x_113);
lean_dec(x_95);
x_114 = l_Lean_Elab_Term_elabSyntheticHole___closed__4;
x_115 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_113);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_92, 1);
lean_inc(x_116);
lean_dec(x_92);
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
lean_dec(x_93);
x_118 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_119);
x_121 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_88, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_86, 4);
lean_inc(x_125);
lean_dec(x_86);
x_126 = l_Lean_indentExpr(x_119);
x_127 = l_Lean_Elab_Term_elabSyntheticHole___closed__6;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1___boxed), 8, 1);
lean_closure_set(x_131, 0, x_130);
x_132 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(x_89, x_125, x_131, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_134 = x_121;
} else {
 lean_dec_ref(x_121);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_119);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
lean_object* x_136; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_31);
lean_ctor_set(x_136, 1, x_87);
return x_136;
}
}
}
}
else
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_137 = 0;
lean_inc(x_5);
x_138 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_137, x_10, x_5, x_6, x_7, x_8, x_9);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_139);
x_141 = l_Lean_Expr_mvarId_x21(x_139);
x_142 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_141, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_140);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
lean_ctor_set(x_142, 0, x_139);
return x_142;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
x_147 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 6);
if (x_147 == 0)
{
uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_148 = 2;
lean_inc(x_5);
x_149 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_148, x_10, x_5, x_6, x_7, x_8, x_9);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_150);
x_152 = l_Lean_Expr_mvarId_x21(x_150);
x_153 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_152, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_151);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_dec(x_155);
lean_ctor_set(x_153, 0, x_150);
return x_153;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_150);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_158 = 0;
lean_inc(x_5);
x_159 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_2, x_158, x_10, x_5, x_6, x_7, x_8, x_9);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_160);
x_162 = l_Lean_Expr_mvarId_x21(x_160);
x_163 = l_Lean_Elab_Term_registerMVarErrorHoleInfo(x_162, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
lean_ctor_set(x_163, 0, x_160);
return x_163;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Term_elabSyntheticHole___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_isDelayedAssigned___at_Lean_Elab_Term_elabSyntheticHole___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("syntheticHole", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSyntheticHole", 17);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSyntheticHole), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(63u);
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(99u);
x_2 = lean_unsigned_to_nat(97u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__1;
x_2 = lean_unsigned_to_nat(37u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__2;
x_4 = lean_unsigned_to_nat(97u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(63u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(63u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__4;
x_2 = lean_unsigned_to_nat(41u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__5;
x_4 = lean_unsigned_to_nat(58u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg), 1, 0);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letMVar", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l_Lean_Elab_Term_elabLetMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetMVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'let_mvar%', metavariable '?", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetMVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetMVar___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetMVar___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has already been used", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetMVar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetMVar___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabLetMVar___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(6u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = lean_st_ref_get(x_8, x_9);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_6, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
lean_inc(x_25);
x_26 = l_Lean_MetavarContext_findUserName_x3f(x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_Elab_Term_elabTerm(x_16, x_27, x_28, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_32 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = 2;
lean_inc(x_5);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_35, x_36, x_25, x_5, x_6, x_7, x_8, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_mvarId_x21(x_38);
x_41 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_40, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_Term_elabTerm(x_18, x_2, x_28, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = l_Lean_Elab_Term_mkSaveInfoAnnotation(x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = l_Lean_Elab_Term_mkSaveInfoAnnotation(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
return x_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_29, 0);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_29);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_2);
x_63 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_63, 0, x_25);
x_64 = l_Lean_Elab_Term_elabLetMVar___closed__4;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Elab_Term_elabLetMVar___closed__6;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabLetMVar", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetMVar), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabLetMVar___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(112u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__4;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__5;
x_4 = lean_unsigned_to_nat(46u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown metavariable '?", 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_getId(x_1);
lean_inc(x_13);
x_14 = l_Lean_MetavarContext_findUserName_x3f(x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_19, x_2, x_3, x_4, x_5, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Expr_mvar___override(x_21);
x_23 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_22, x_2, x_3, x_4, x_5, x_11);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("waitIfTypeMVar", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_infer_type(x_18, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_23 = l_Lean_Elab_Term_tryPostponeIfMVar(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = l_Lean_Elab_Term_elabTerm(x_16, x_2, x_25, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabWaitIfTypeMVar", 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabWaitIfTypeMVar), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(125u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(60u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__5;
x_4 = lean_unsigned_to_nat(60u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_11, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("waitIfTypeContainsMVar", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_infer_type(x_18, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_hasExprMVar(x_24);
lean_dec(x_24);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
x_27 = 1;
x_28 = l_Lean_Elab_Term_elabTerm(x_16, x_2, x_27, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_28;
}
else
{
lean_object* x_29; 
lean_inc(x_3);
x_29 = l_Lean_Elab_Term_tryPostpone(x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 1;
x_32 = l_Lean_Elab_Term_elabTerm(x_16, x_2, x_31, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabWaitIfTypeContainsMVar", 26);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabWaitIfTypeContainsMVar), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(127u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(133u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__1;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(127u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(127u);
x_2 = lean_unsigned_to_nat(76u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__4;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__5;
x_4 = lean_unsigned_to_nat(76u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("waitIfContainsMVar", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWaitIfContainsMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_hasExprMVar(x_18);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = l_Lean_Elab_Term_elabTerm(x_16, x_2, x_21, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_3);
x_23 = l_Lean_Elab_Term_tryPostpone(x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = l_Lean_Elab_Term_elabTerm(x_16, x_2, x_25, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabWaitIfContainsMVar", 22);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabWaitIfContainsMVar), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(135u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(141u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__1;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(135u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(135u);
x_2 = lean_unsigned_to_nat(68u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__4;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__5;
x_4 = lean_unsigned_to_nat(68u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkTacticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = 2;
x_12 = lean_box(0);
lean_inc(x_5);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Expr_mvarId_x21(x_14);
x_17 = lean_ctor_get(x_7, 5);
lean_inc(x_17);
x_18 = l_Lean_Elab_Term_saveContext(x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_registerSyntheticMVar(x_17, x_16, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_7);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkTacticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkTacticMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabByTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'by' tactic, expected type has not been provided", 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabByTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabByTactic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabByTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabByTactic___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabByTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_tryPostpone(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_elabByTactic___closed__3;
x_13 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkTacticMVar(x_18, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabByTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabByTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("byTactic", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabByTactic", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabByTactic___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(150u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(155u);
x_2 = lean_unsigned_to_nat(75u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__1;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__2;
x_4 = lean_unsigned_to_nat(75u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(150u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(150u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__4;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__5;
x_4 = lean_unsigned_to_nat(46u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoImplicitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = 1;
x_14 = l_Lean_Elab_Term_elabTerm(x_11, x_12, x_13, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = l_Lean_Elab_Term_mkNoImplicitLambdaAnnotation(x_16);
lean_ctor_set(x_2, 0, x_17);
x_18 = 1;
x_19 = l_Lean_Elab_Term_elabTerm(x_11, x_2, x_18, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Elab_Term_mkNoImplicitLambdaAnnotation(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = 1;
x_24 = l_Lean_Elab_Term_elabTerm(x_11, x_22, x_23, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNoImplicitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabNoImplicitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("noImplicitLambda", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabNoImplicitLambda", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNoImplicitLambda___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(157u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(158u);
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__2;
x_4 = lean_unsigned_to_nat(66u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(157u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(157u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__5;
x_4 = lean_unsigned_to_nat(62u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)", 91);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabBadCDot___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Term_elabBadCDot___rarg___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBadCDot___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_elabBadCDot___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBadCDot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_elabBadCDot(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cdot", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabBadCDot", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBadCDot___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(160u);
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(161u);
x_2 = lean_unsigned_to_nat(104u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__1;
x_2 = lean_unsigned_to_nat(26u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__2;
x_4 = lean_unsigned_to_nat(104u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(160u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(160u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__4;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__5;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed syntax", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStrLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_isStrLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkStrLit(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabStrLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabStrLit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("str", 3);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabStrLit", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStrLit___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(163u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(166u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__1;
x_2 = lean_unsigned_to_nat(25u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(163u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(163u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__4;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__5;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(0);
lean_inc(x_4);
x_11 = l_Lean_Meta_mkFreshTypeMVar(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_16);
x_19 = l_Lean_Meta_isExprDefEq(x_18, x_16, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNumLit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabNumLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabNumLit___spec__2(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNumLit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Lean_Meta_getDecLevel(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Term_elabNumLit___lambda__1___closed__2;
lean_inc(x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_18);
x_21 = l_Lean_mkRawNatLit(x_3);
lean_inc(x_21);
lean_inc(x_12);
x_22 = l_Lean_mkAppB(x_20, x_12, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Elab_Term_mkInstMVar(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_elabNumLit___lambda__1___closed__4;
x_27 = l_Lean_Expr_const___override(x_26, x_18);
lean_inc(x_24);
x_28 = l_Lean_mkApp3(x_27, x_12, x_21, x_24);
x_29 = l_Lean_Expr_mvarId_x21(x_24);
lean_inc(x_28);
x_30 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_29, x_2, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabNumLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_isNatLit_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabNumLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Elab_Term_elabNumLit___lambda__1(x_2, x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNumLit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabNumLit___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabNumLit", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNumLit), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(175u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(184u);
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__1;
x_2 = lean_unsigned_to_nat(25u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__2;
x_4 = lean_unsigned_to_nat(10u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(175u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(175u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__4;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__5;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRawNatLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isNatLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkRawNatLit(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabRawNatLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabRawNatLit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rawNatLit", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabRawNatLit", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawNatLit___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(186u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(189u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(186u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(186u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__4;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__5;
x_4 = lean_unsigned_to_nat(48u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfScientific", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabScientificLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofScientific", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabScientificLit___closed__1;
x_2 = l_Lean_Elab_Term_elabScientificLit___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabScientificLit___closed__5;
x_2 = l_Lean_Elab_Term_elabScientificLit___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabScientificLit___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabScientificLit___closed__5;
x_2 = l_Lean_Elab_Term_elabScientificLit___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabScientificLit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabScientificLit___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabScientificLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_isScientificLit_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkFreshTypeMVarFor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_20 = l_Lean_Meta_getDecLevel(x_18, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Term_elabScientificLit___closed__2;
lean_inc(x_24);
x_26 = l_Lean_Expr_const___override(x_25, x_24);
lean_inc(x_18);
x_27 = l_Lean_Expr_app___override(x_26, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Elab_Term_mkInstMVar(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_elabScientificLit___closed__4;
x_32 = l_Lean_Expr_const___override(x_31, x_24);
x_33 = l_Lean_mkRawNatLit(x_14);
x_34 = l_Lean_mkRawNatLit(x_16);
lean_inc(x_29);
x_35 = l_Lean_Expr_mvarId_x21(x_29);
x_36 = lean_unbox(x_15);
lean_dec(x_15);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = l_Lean_Elab_Term_elabScientificLit___closed__8;
x_38 = l_Lean_mkApp5(x_32, x_18, x_29, x_33, x_37, x_34);
lean_inc(x_38);
x_39 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_35, x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_Lean_Elab_Term_elabScientificLit___closed__11;
x_45 = l_Lean_mkApp5(x_32, x_18, x_29, x_33, x_44, x_34);
lean_inc(x_45);
x_46 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_35, x_1, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_20);
if (x_55 == 0)
{
return x_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("scientific", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabScientificLit", 17);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabScientificLit), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(192u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(201u);
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__2;
x_4 = lean_unsigned_to_nat(12u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(192u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(192u);
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__5;
x_4 = lean_unsigned_to_nat(21u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCharLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Char", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCharLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabCharLit___closed__1;
x_2 = l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCharLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabCharLit___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCharLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_isCharLit_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unbox_uint32(x_12);
lean_dec(x_12);
x_14 = lean_uint32_to_nat(x_13);
x_15 = l_Lean_mkRawNatLit(x_14);
x_16 = l_Lean_Elab_Term_elabCharLit___closed__3;
x_17 = l_Lean_Expr_app___override(x_16, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCharLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCharLit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("char", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabCharLit", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCharLit___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(203u);
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(206u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__1;
x_2 = lean_unsigned_to_nat(26u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(203u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(203u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__4;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__5;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabQuotedName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isNameLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabQuotedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabQuotedName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("quotedName", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabQuotedName", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabQuotedName___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(208u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(211u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__1;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(208u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(208u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__4;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__5;
x_4 = lean_unsigned_to_nat(50u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveLocalName_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(x_10, x_12);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5___lambda__1(x_13, x_12, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_17 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_10);
x_12 = l_List_isEmpty___rarg(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 5);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_6, 5, x_16);
x_17 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
x_27 = lean_ctor_get(x_6, 9);
x_28 = lean_ctor_get(x_6, 10);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_29 = l_Lean_replaceRef(x_1, x_23);
lean_dec(x_23);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_24);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set(x_30, 8, x_26);
lean_ctor_set(x_30, 9, x_27);
lean_ctor_set(x_30, 10, x_28);
x_31 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5(x_9, x_2, x_3, x_4, x_5, x_30, x_7, x_8);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3;
x_33 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__4(x_1, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous identifier '", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: ", 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_15 = l_Lean_Syntax_formatStxAux(x_12, x_13, x_14, x_1);
x_16 = l_Std_Format_defWidth;
x_17 = lean_format_pretty(x_15, x_16);
x_18 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at_Lean_resolveGlobalConstNoOverload___spec__1(x_10, x_22);
x_24 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_23);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
x_26 = l_Lean_Elab_Term_elabSyntheticHole___closed__7;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_9, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_box(0);
x_40 = 0;
x_41 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_42 = l_Lean_Syntax_formatStxAux(x_39, x_40, x_41, x_1);
x_43 = l_Std_Format_defWidth;
x_44 = lean_format_pretty(x_42, x_43);
x_45 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_box(0);
x_50 = l_List_mapTR_loop___at_Lean_resolveGlobalConstNoOverload___spec__1(x_10, x_49);
x_51 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_50);
x_52 = lean_string_append(x_48, x_51);
lean_dec(x_51);
x_53 = l_Lean_Elab_Term_elabSyntheticHole___closed__7;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7(x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_4);
x_11 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = l_Lean_LocalContext_empty;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 6);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
lean_inc(x_11);
x_22 = l_Lean_Elab_addConstInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__8(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_11);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDoubleQuotedName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabDoubleQuotedName___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabDoubleQuotedName___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_addConstInfo___at_Lean_Elab_Term_elabDoubleQuotedName___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDoubleQuotedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabDoubleQuotedName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("doubleQuotedName", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabDoubleQuotedName", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDoubleQuotedName___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(213u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(214u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__2;
x_4 = lean_unsigned_to_nat(63u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(213u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(213u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__5;
x_4 = lean_unsigned_to_nat(62u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid `decl_name%` macro, the declaration name is not available", 65);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Term_getDeclName_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__10(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_quoteNameMk(x_16);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_16);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3;
x_22 = l_String_intercalate(x_21, x_20);
x_23 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_box(2);
x_26 = l_Lean_Syntax_mkNameLit(x_24, x_25);
x_27 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5;
x_28 = lean_array_push(x_27, x_26);
x_29 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_box(0);
lean_inc(x_32);
x_34 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_quoteNameMk(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_32);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3;
x_39 = l_String_intercalate(x_38, x_37);
x_40 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = lean_box(2);
x_43 = l_Lean_Syntax_mkNameLit(x_41, x_42);
x_44 = l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5;
x_45 = lean_array_push(x_44, x_43);
x_46 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_31);
return x_48;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDeclName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDeclName___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabDeclName___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDeclName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabDeclName___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declName", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabDeclName", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDeclName), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(216u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(219u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__1;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__2;
x_4 = lean_unsigned_to_nat(32u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(216u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(216u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__4;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__5;
x_4 = lean_unsigned_to_nat(46u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_7, 6);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_box(x_19);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_21);
if (x_16 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Name_append(x_13, x_12);
lean_dec(x_13);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___rarg), 9, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_18, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___rarg), 9, 2);
lean_closure_set(x_26, 0, x_12);
lean_closure_set(x_26, 1, x_22);
x_27 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_18, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_27;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withDeclName", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabWithDeclName", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabWithDeclName), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(221u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(225u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__1;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__2;
x_4 = lean_unsigned_to_nat(73u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(221u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(221u);
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__4;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__5;
x_4 = lean_unsigned_to_nat(66u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
x_13 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_elabTerm(x_11, x_12, x_13, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_infer_type(x_15, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTypeOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabTypeOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeOf", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabTypeOf", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeOf___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(227u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(228u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(227u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(227u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__5;
x_4 = lean_unsigned_to_nat(42u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_silent", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Term_isTacticOrPostponedHole_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2;
x_18 = l_Lean_mkAnnotation(x_17, x_1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2;
x_21 = l_Lean_mkAnnotation(x_20, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureTypeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isStrLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_box(0);
x_19 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Elab_Term_elabTerm(x_17, x_18, x_19, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = lean_infer_type(x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
lean_ctor_set(x_12, 0, x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_Elab_Term_elabTermEnsuringType(x_27, x_12, x_19, x_19, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_12, 0);
lean_inc(x_45);
lean_dec(x_12);
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_Syntax_getArg(x_1, x_46);
x_48 = lean_box(0);
x_49 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_50 = l_Lean_Elab_Term_elabTerm(x_47, x_48, x_49, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = lean_infer_type(x_51, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(3u);
x_57 = l_Lean_Syntax_getArg(x_1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_54);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_45);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = l_Lean_Elab_Term_elabTermEnsuringType(x_57, x_58, x_49, x_49, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_70 = x_53;
} else {
 lean_dec_ref(x_53);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_ctor_get(x_50, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_50, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_74 = x_50;
} else {
 lean_dec_ref(x_50);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureTypeOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabEnsureTypeOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ensureTypeOf", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabEnsureTypeOf", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabEnsureTypeOf___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(258u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(265u);
x_2 = lean_unsigned_to_nat(97u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__2;
x_4 = lean_unsigned_to_nat(97u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(258u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(258u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__4;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__5;
x_4 = lean_unsigned_to_nat(54u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isStrLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = 1;
x_18 = l_Lean_Elab_Term_elabTermEnsuringType(x_16, x_2, x_17, x_17, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = 1;
x_24 = l_Lean_Elab_Term_elabTermEnsuringType(x_21, x_2, x_23, x_23, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabEnsureExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabEnsureExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ensureExpectedType", 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabEnsureExpectedType", 22);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabEnsureExpectedType___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(267u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(270u);
x_2 = lean_unsigned_to_nat(82u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__1;
x_2 = lean_unsigned_to_nat(40u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__2;
x_4 = lean_unsigned_to_nat(82u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(267u);
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(267u);
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__4;
x_2 = lean_unsigned_to_nat(44u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__5;
x_4 = lean_unsigned_to_nat(66u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_5, x_7);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 1);
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_20);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2(x_1, x_2, x_3, x_18, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_8, 0, x_26);
lean_ctor_set(x_22, 0, x_8);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_8, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_20);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_31);
lean_ctor_set(x_8, 0, x_4);
x_32 = 1;
x_33 = lean_usize_add(x_7, x_32);
x_7 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_35);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2(x_1, x_2, x_3, x_18, x_35, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_7, x_46);
x_7 = x_47;
x_8 = x_45;
x_15 = x_43;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_19 = x_7;
} else {
 lean_dec_ref(x_7);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_31; 
lean_inc(x_18);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_18);
x_20 = x_31;
x_21 = x_14;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = l_Lean_LocalDecl_fvarId(x_32);
x_34 = lean_name_eq(x_33, x_1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_localDeclDependsOn___at_Lean_Elab_Term_addAutoBoundImplicits_go___spec__1(x_32, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_2);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_2);
x_20 = x_39;
x_21 = x_38;
goto block_30;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3;
x_20 = x_41;
x_21 = x_40;
goto block_30;
}
}
else
{
lean_object* x_42; 
lean_dec(x_32);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_2);
x_20 = x_42;
x_21 = x_14;
goto block_30;
}
}
block_30:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_19;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_18);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
lean_inc(x_3);
if (lean_is_scalar(x_19)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_19;
}
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_6 = x_28;
x_7 = x_26;
x_14 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_array_get_size(x_13);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_9);
lean_inc(x_6);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__3(x_1, x_2, x_3, x_14, x_13, x_17, x_18, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1(x_23, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_9);
lean_dec(x_6);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_array_get_size(x_32);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4(x_1, x_2, x_33, x_32, x_36, x_37, x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1(x_42, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_9);
lean_dec(x_6);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_19 = x_7;
} else {
 lean_dec_ref(x_7);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_32; 
lean_inc(x_18);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_18);
x_20 = x_32;
x_21 = x_14;
goto block_31;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l_Lean_LocalDecl_fvarId(x_33);
x_35 = lean_name_eq(x_34, x_1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_localDeclDependsOn___at_Lean_Elab_Term_addAutoBoundImplicits_go___spec__1(x_33, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_2);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_20 = x_40;
x_21 = x_39;
goto block_31;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3;
x_20 = x_42;
x_21 = x_41;
goto block_31;
}
}
else
{
lean_object* x_43; 
lean_dec(x_33);
lean_inc(x_2);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_2);
x_20 = x_43;
x_21 = x_14;
goto block_31;
}
}
block_31:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (lean_is_scalar(x_19)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_19;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_18);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_inc(x_3);
if (lean_is_scalar(x_19)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_19;
}
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_6, x_28);
x_6 = x_29;
x_7 = x_27;
x_14 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Elab_Term_elabClear___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2(x_1, x_2, x_4, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_array_get_size(x_23);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__5(x_1, x_2, x_24, x_23, x_27, x_28, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_elabClear___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__13(x_1, x_3, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_13);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_13);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__14(x_1, x_13, x_20, x_21);
lean_dec(x_13);
return x_22;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__15(x_1, x_5, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_eq(x_1, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_8);
x_9 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_8, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_MetavarContext_getDecl(x_14, x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11(x_1, x_17);
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = l_Lean_MetavarContext_getDecl(x_21, x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11(x_1, x_24);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_29, x_28);
return x_30;
}
}
case 5:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_getAppFn(x_2);
x_32 = l_Lean_Expr_isMVar(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10(x_1, x_2, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_2);
x_34 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_getAppFn(x_35);
x_38 = lean_expr_eqv(x_37, x_31);
lean_dec(x_31);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_2);
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_40; 
lean_dec(x_35);
x_40 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10(x_1, x_2, x_36);
return x_40;
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_41, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_42, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_52, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_53, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_53);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_63, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_64, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_65, x_73);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_65);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_70, 0);
lean_dec(x_76);
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_64);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_66, 0);
lean_dec(x_80);
return x_66;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_dec(x_66);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_84 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_83, x_3);
return x_84;
}
case 11:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
lean_dec(x_2);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_85, x_3);
return x_86;
}
default: 
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__9(x_1, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__21(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__22(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__21(x_1, x_3, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_13);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_13);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__22(x_1, x_13, x_20, x_21);
lean_dec(x_13);
return x_22;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__23(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__23(x_1, x_5, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_eq(x_1, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_8);
x_9 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_8, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_MetavarContext_getDecl(x_14, x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19(x_1, x_17);
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = l_Lean_MetavarContext_getDecl(x_21, x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19(x_1, x_24);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_29, x_28);
return x_30;
}
}
case 5:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_getAppFn(x_2);
x_32 = l_Lean_Expr_isMVar(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18(x_1, x_2, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_2);
x_34 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_getAppFn(x_35);
x_38 = lean_expr_eqv(x_37, x_31);
lean_dec(x_31);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_2);
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_40; 
lean_dec(x_35);
x_40 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18(x_1, x_2, x_36);
return x_40;
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_41, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_42, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_52, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_53, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_53);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_63, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_64, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_65, x_73);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_65);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_70, 0);
lean_dec(x_76);
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_64);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_66, 0);
lean_dec(x_80);
return x_66;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_dec(x_66);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_84 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_83, x_3);
return x_84;
}
case 11:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
lean_dec(x_2);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_85, x_3);
return x_86;
}
default: 
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__17(x_1, x_2, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___closed__1;
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Expr_hasFVar(x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_1);
x_20 = lean_st_ref_get(x_8, x_14);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_15);
x_27 = lean_st_ref_set(x_6, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_23, 2);
x_38 = lean_ctor_get(x_23, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_st_ref_set(x_6, x_39, x_24);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = 0;
x_44 = lean_box(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_15);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_2, x_1, x_17);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_get(x_8, x_14);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_take(x_6, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
lean_ctor_set(x_53, 0, x_49);
x_57 = lean_st_ref_set(x_6, x_53, x_54);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_48);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_53, 1);
x_63 = lean_ctor_get(x_53, 2);
x_64 = lean_ctor_get(x_53, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_st_ref_set(x_6, x_65, x_54);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_15);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_2, x_1, x_17);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_st_ref_get(x_8, x_14);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_ref_take(x_6, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_77, 0);
lean_dec(x_80);
lean_ctor_set(x_77, 0, x_73);
x_81 = lean_st_ref_set(x_6, x_77, x_78);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_72);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_77, 1);
x_87 = lean_ctor_get(x_77, 2);
x_88 = lean_ctor_get(x_77, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_73);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_6, x_89, x_78);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_72);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabClear___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabClear___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabClear___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_elabClear___lambda__2___closed__1;
lean_inc(x_6);
lean_inc(x_3);
x_13 = l_Lean_PersistentArray_forIn___at_Lean_Elab_Term_elabClear___spec__1(x_1, x_12, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Elab_Term_elabClear___lambda__2___closed__2;
x_18 = lean_box(0);
x_19 = lean_apply_8(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabClear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("not in scope", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabClear___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabClear___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Elab_Term_isLocalIdent_x3f(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_elabClear___closed__2;
x_16 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabPipeCompletion___spec__1(x_11, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_50 = l_Lean_Elab_Term_elabClear___lambda__2(x_19, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_22 = x_53;
x_23 = x_52;
goto block_48;
}
else
{
uint8_t x_54; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
x_59 = l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7(x_58, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_64 = l_Lean_Elab_Term_elabClear___lambda__2(x_19, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_22 = x_67;
x_23 = x_66;
goto block_48;
}
else
{
uint8_t x_68; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_dec(x_59);
x_73 = 0;
x_22 = x_73;
x_23 = x_72;
goto block_48;
}
}
block_48:
{
if (x_22 == 0)
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_19);
x_24 = 1;
x_25 = l_Lean_Elab_Term_elabTerm(x_21, x_2, x_24, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_19);
x_27 = lean_local_ctx_erase(x_26, x_19);
x_28 = l_Lean_Meta_getLocalInstances(x_5, x_6, x_7, x_8, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_array_get_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_box(x_34);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_37, 0, x_21);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_35);
lean_closure_set(x_37, 3, x_36);
if (x_33 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
x_38 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_39 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(x_27, x_38, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_31, x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
x_41 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_42 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(x_27, x_41, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_42;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_45 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_elabClear___spec__6(x_19, x_29, x_43, x_44, x_45);
lean_dec(x_29);
lean_dec(x_19);
x_47 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(x_27, x_46, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_47;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__3(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Elab_Term_elabClear___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__5(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Elab_Term_elabClear___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Elab_Term_elabClear___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_elabClear___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_elabClear___spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__10(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__13(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__14(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__12(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__15(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__11(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Elab_Term_elabClear___spec__18(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__21(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__22(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at_Lean_Elab_Term_elabClear___spec__20(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabClear___spec__23(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at_Lean_Elab_Term_elabClear___spec__19(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Elab_Term_elabClear___spec__17(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Elab_Term_elabClear___spec__16(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabClear___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabClear___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabClear___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabClear(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clear", 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabClear___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabClear", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabClear___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabClear___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabClear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabClear___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabClear___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabClear___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(272u);
x_2 = lean_unsigned_to_nat(27u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(290u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__1;
x_2 = lean_unsigned_to_nat(27u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(272u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(272u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__4;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__5;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabClear_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabClear___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__5;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__7;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__8;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__11;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_st_ref_take(x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 4);
lean_dec(x_20);
x_21 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_14, x_19);
lean_dec(x_14);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
lean_ctor_set(x_16, 4, x_22);
lean_ctor_set(x_16, 0, x_21);
x_23 = lean_st_ref_set(x_10, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_10, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
lean_ctor_set(x_28, 1, x_32);
x_33 = lean_st_ref_set(x_8, x_28, x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_37 = lean_box(0);
x_3 = x_36;
x_4 = x_37;
x_11 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 2);
x_41 = lean_ctor_get(x_28, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_st_ref_set(x_8, x_43, x_29);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_48 = lean_box(0);
x_3 = x_47;
x_4 = x_48;
x_11 = x_45;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
x_52 = lean_ctor_get(x_16, 2);
x_53 = lean_ctor_get(x_16, 3);
x_54 = lean_ctor_get(x_16, 5);
x_55 = lean_ctor_get(x_16, 6);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_56 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_14, x_50);
lean_dec(x_14);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
x_58 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set(x_58, 6, x_55);
x_59 = lean_st_ref_set(x_10, x_58, x_17);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_10, x_60);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_8, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 3);
lean_inc(x_68);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
x_70 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 4, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_68);
x_72 = lean_st_ref_set(x_8, x_71, x_65);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = 1;
x_75 = lean_usize_add(x_3, x_74);
x_76 = lean_box(0);
x_3 = x_75;
x_4 = x_76;
x_11 = x_73;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_scopedEnvExtensionsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2(x_12, x_15, x_16, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabOpen___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_26 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_23);
lean_ctor_set(x_27, 9, x_24);
lean_ctor_set(x_27, 10, x_25);
x_28 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8(x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_10);
lean_dec(x_9);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown namespace '", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_9, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_3, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = l_Lean_ResolveName_resolveNamespace(x_14, x_20, x_27, x_1);
lean_dec(x_20);
if (x_2 == 0)
{
uint8_t x_29; 
x_29 = l_List_isEmpty___rarg(x_28);
if (x_29 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_28);
lean_free_object(x_23);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_1, x_30);
x_32 = l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_dec(x_1);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_1);
x_46 = l_Lean_ResolveName_resolveNamespace(x_14, x_20, x_45, x_1);
lean_dec(x_20);
if (x_2 == 0)
{
uint8_t x_47; 
x_47 = l_List_isEmpty___rarg(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
x_49 = 1;
x_50 = l_Lean_Name_toString(x_1, x_49);
x_51 = l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10(x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; 
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_44);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Term_elabOpen___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = l_List_filterMap___at_Lean_resolveNamespace___spec__1(x_11);
x_13 = l_List_isEmpty___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_7, 5);
x_17 = l_Lean_replaceRef(x_1, x_16);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_17);
x_18 = 0;
x_19 = l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9(x_10, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
x_27 = lean_ctor_get(x_7, 7);
x_28 = lean_ctor_get(x_7, 8);
x_29 = lean_ctor_get(x_7, 9);
x_30 = lean_ctor_get(x_7, 10);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_31 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set(x_32, 7, x_27);
lean_ctor_set(x_32, 8, x_28);
lean_ctor_set(x_32, 9, x_29);
lean_ctor_set(x_32, 10, x_30);
x_33 = 0;
x_34 = l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9(x_10, x_33, x_2, x_3, x_4, x_5, x_6, x_32, x_8, x_9);
lean_dec(x_8);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3;
x_36 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabOpen___spec__7(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous namespace '", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: '", 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Term_elabOpen___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_13, x_14);
x_16 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_11);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_36 = 1;
x_37 = l_Lean_Name_toString(x_35, x_36);
x_38 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_11);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_elabOpen___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_8, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_2, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_ResolveName_resolveGlobalName(x_13, x_19, x_25, x_1);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_ResolveName_resolveGlobalName(x_13, x_19, x_29, x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabOpen___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_1, x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_10 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_elabOpen___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(x_11, x_13);
x_15 = l_List_isEmpty___rarg(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14___lambda__1(x_14, x_13, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_14);
x_18 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabOpen___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Term_elabOpen___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Expr_const___override(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Term_elabOpen___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Expr_const___override(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Term_elabOpen___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = lean_expr_dbg_to_string(x_14);
lean_dec(x_14);
x_16 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_List_mapTR_loop___at_Lean_Elab_Term_elabOpen___spec__18(x_13, x_11, x_13);
x_21 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_elabSyntheticHole___closed__7;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_10, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_28);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = l_Lean_Expr_const___override(x_1, x_36);
x_38 = lean_expr_dbg_to_string(x_37);
lean_dec(x_37);
x_39 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_List_mapTR_loop___at_Lean_Elab_Term_elabOpen___spec__20(x_36, x_11, x_36);
x_44 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec(x_44);
x_46 = l_Lean_Elab_Term_elabSyntheticHole___closed__7;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_10);
if (x_51 == 0)
{
return x_10;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Term_elabOpen___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Syntax_getId(x_2);
x_12 = l_Lean_Name_append(x_1, x_11);
lean_dec(x_1);
x_13 = lean_st_ref_get(x_9, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
x_18 = l_Lean_Environment_contains(x_17, x_12);
if (x_18 == 0)
{
uint8_t x_19; 
lean_free_object(x_13);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 5);
x_21 = l_Lean_replaceRef(x_2, x_20);
lean_dec(x_20);
lean_dec(x_2);
lean_ctor_set(x_8, 5, x_21);
x_22 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Term_elabOpen___spec__13(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 4);
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 6);
x_30 = lean_ctor_get(x_8, 7);
x_31 = lean_ctor_get(x_8, 8);
x_32 = lean_ctor_get(x_8, 9);
x_33 = lean_ctor_get(x_8, 10);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_34 = l_Lean_replaceRef(x_2, x_28);
lean_dec(x_28);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_30);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_35, 9, x_32);
lean_ctor_set(x_35, 10, x_33);
x_36 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Term_elabOpen___spec__13(x_12, x_3, x_4, x_5, x_6, x_7, x_35, x_9, x_16);
return x_36;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_12);
x_40 = l_Lean_Environment_contains(x_39, x_12);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_8, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_8, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_8, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_8, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_8, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 10);
lean_inc(x_51);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 lean_ctor_release(x_8, 6);
 lean_ctor_release(x_8, 7);
 lean_ctor_release(x_8, 8);
 lean_ctor_release(x_8, 9);
 lean_ctor_release(x_8, 10);
 x_52 = x_8;
} else {
 lean_dec_ref(x_8);
 x_52 = lean_box(0);
}
x_53 = l_Lean_replaceRef(x_2, x_46);
lean_dec(x_46);
lean_dec(x_2);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 11, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_44);
lean_ctor_set(x_54, 4, x_45);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_47);
lean_ctor_set(x_54, 7, x_48);
lean_ctor_set(x_54, 8, x_49);
lean_ctor_set(x_54, 9, x_50);
lean_ctor_set(x_54, 10, x_51);
x_55 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Term_elabOpen___spec__13(x_12, x_3, x_4, x_5, x_6, x_7, x_54, x_9, x_38);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_38);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_st_ref_set(x_2, x_13, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_st_ref_set(x_2, x_28, x_14);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__22(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Term_elabOpen___spec__12(x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Syntax_getId(x_18);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_box(0);
x_4 = x_27;
x_5 = x_28;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__24(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
x_17 = lean_st_ref_take(x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 4);
lean_dec(x_22);
lean_inc(x_1);
x_23 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_16, x_21, x_1);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
lean_ctor_set(x_18, 4, x_24);
lean_ctor_set(x_18, 0, x_23);
x_25 = lean_st_ref_set(x_12, x_18, x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_12, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_10, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
lean_ctor_set(x_30, 1, x_34);
x_35 = lean_st_ref_set(x_10, x_30, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_38 = lean_usize_add(x_4, x_37);
x_39 = lean_box(0);
x_4 = x_38;
x_5 = x_39;
x_13 = x_36;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 2);
x_43 = lean_ctor_get(x_30, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = lean_st_ref_set(x_10, x_45, x_31);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = 1;
x_49 = lean_usize_add(x_4, x_48);
x_50 = lean_box(0);
x_4 = x_49;
x_5 = x_50;
x_13 = x_47;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
x_54 = lean_ctor_get(x_18, 2);
x_55 = lean_ctor_get(x_18, 3);
x_56 = lean_ctor_get(x_18, 5);
x_57 = lean_ctor_get(x_18, 6);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
lean_inc(x_1);
x_58 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_16, x_52, x_1);
x_59 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
x_60 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_56);
lean_ctor_set(x_60, 6, x_57);
x_61 = lean_st_ref_set(x_12, x_60, x_19);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_12, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_take(x_10, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 3);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
x_72 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 4, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set(x_73, 3, x_70);
x_74 = lean_st_ref_set(x_10, x_73, x_67);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = 1;
x_77 = lean_usize_add(x_4, x_76);
x_78 = lean_box(0);
x_4 = x_77;
x_5 = x_78;
x_13 = x_75;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_box(0);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__24(x_1, x_14, x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__25(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_17 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Term_elabOpen___spec__12(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_box(0);
x_4 = x_20;
x_5 = x_21;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Term_elabOpen___spec__12(x_13, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_push(x_17, x_19);
lean_ctor_set(x_3, 1, x_21);
x_2 = x_14;
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_array_push(x_16, x_23);
lean_ctor_set(x_3, 0, x_25);
x_2 = x_14;
x_11 = x_24;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_29 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Term_elabOpen___spec__12(x_13, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_push(x_28, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_2 = x_14;
x_3 = x_33;
x_11 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_array_push(x_27, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
x_2 = x_14;
x_3 = x_38;
x_11 = x_36;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 5);
x_5 = 0;
x_6 = l_Lean_Syntax_getPos_x3f(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg___boxed), 3, 0);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg(x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Exception_getRef(x_1);
x_14 = 0;
x_15 = l_Lean_Syntax_getPos_x3f(x_13, x_14);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_nat_dec_eq(x_12, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_19 = lean_ctor_get(x_7, 1);
x_20 = l_Lean_FileMap_toPosition(x_19, x_17);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = l_Nat_repr(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Nat_repr(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Exception_toMessageData(x_1);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_10, 0, x_38);
return x_10;
}
else
{
lean_object* x_39; 
lean_dec(x_17);
x_39 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_10, 0, x_39);
return x_10;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = l_Lean_Exception_getRef(x_1);
x_43 = 0;
x_44 = l_Lean_Syntax_getPos_x3f(x_42, x_43);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
x_45 = l_Lean_Exception_toMessageData(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_nat_dec_eq(x_40, x_47);
lean_dec(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_49 = lean_ctor_get(x_7, 1);
x_50 = l_Lean_FileMap_toPosition(x_49, x_47);
lean_dec(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = l_Nat_repr(x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
x_60 = l_Nat_repr(x_59);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Exception_toMessageData(x_1);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_41);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_47);
x_70 = l_Lean_Exception_toMessageData(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_41);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_elabOpen___spec__31(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_16, x_2, x_18);
x_2 = x_21;
x_3 = x_22;
x_11 = x_19;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", errors ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_elabOpen___spec__31(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
x_19 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_toMessageList(x_15);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_15 = l_Lean_Syntax_getId(x_2);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__1;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__2(x_21, x_22, x_1);
x_24 = lean_array_to_list(lean_box(0), x_23);
x_25 = lean_box(0);
x_26 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_24, x_25);
x_27 = l_Lean_MessageData_ofList(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 5);
x_33 = l_Lean_replaceRef(x_2, x_32);
lean_dec(x_32);
lean_ctor_set(x_9, 5, x_33);
x_34 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
x_37 = lean_ctor_get(x_9, 2);
x_38 = lean_ctor_get(x_9, 3);
x_39 = lean_ctor_get(x_9, 4);
x_40 = lean_ctor_get(x_9, 5);
x_41 = lean_ctor_get(x_9, 6);
x_42 = lean_ctor_get(x_9, 7);
x_43 = lean_ctor_get(x_9, 8);
x_44 = lean_ctor_get(x_9, 9);
x_45 = lean_ctor_get(x_9, 10);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_46 = l_Lean_replaceRef(x_2, x_40);
lean_dec(x_40);
x_47 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set(x_47, 4, x_39);
lean_ctor_set(x_47, 5, x_46);
lean_ctor_set(x_47, 6, x_41);
lean_ctor_set(x_47, 7, x_42);
lean_ctor_set(x_47, 8, x_43);
lean_ctor_set(x_47, 9, x_44);
lean_ctor_set(x_47, 10, x_45);
x_48 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(x_30, x_4, x_5, x_6, x_7, x_8, x_47, x_10, x_11);
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_5);
return x_48;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_12);
lean_dec(x_12);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_51 = l_Lean_instInhabitedName;
x_52 = l___private_Init_Util_0__outOfBounds___rarg(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_11);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_1, x_49);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to open", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_12 = l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__27(x_2, x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_get_size(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_lengthTRAux___rarg(x_1, x_19);
lean_dec(x_1);
x_21 = lean_nat_dec_eq(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1(x_17, x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
lean_dec(x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_18, x_24);
if (x_25 == 0)
{
uint8_t x_62; 
x_62 = 0;
x_26 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = 1;
x_26 = x_63;
goto block_61;
}
block_61:
{
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_8, 5);
x_29 = l_Lean_replaceRef(x_2, x_28);
lean_dec(x_28);
lean_dec(x_2);
lean_ctor_set(x_8, 5, x_29);
x_30 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4;
x_31 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28(x_30, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
x_38 = lean_ctor_get(x_8, 2);
x_39 = lean_ctor_get(x_8, 3);
x_40 = lean_ctor_get(x_8, 4);
x_41 = lean_ctor_get(x_8, 5);
x_42 = lean_ctor_get(x_8, 6);
x_43 = lean_ctor_get(x_8, 7);
x_44 = lean_ctor_get(x_8, 8);
x_45 = lean_ctor_get(x_8, 9);
x_46 = lean_ctor_get(x_8, 10);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_47 = l_Lean_replaceRef(x_2, x_41);
lean_dec(x_41);
lean_dec(x_2);
x_48 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_48, 2, x_38);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set(x_48, 4, x_40);
lean_ctor_set(x_48, 5, x_47);
lean_ctor_set(x_48, 6, x_42);
lean_ctor_set(x_48, 7, x_43);
lean_ctor_set(x_48, 8, x_44);
lean_ctor_set(x_48, 9, x_45);
lean_ctor_set(x_48, 10, x_46);
x_49 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4;
x_50 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28(x_49, x_16, x_3, x_4, x_5, x_6, x_7, x_48, x_9, x_14);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_16);
x_56 = l_Lean_instInhabitedException;
x_57 = l___private_Init_Util_0__outOfBounds___rarg(x_56);
if (lean_is_scalar(x_15)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_15;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_14);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_array_fget(x_16, x_19);
lean_dec(x_16);
if (lean_is_scalar(x_15)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_15;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
return x_60;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__32(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Syntax_getId(x_16);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_26 = lean_box(0);
x_4 = x_25;
x_5 = x_26;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_1 = x_13;
x_2 = x_16;
x_10 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__34(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_resolveNamespace___at_Lean_Elab_Term_elabOpen___spec__6(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__33(x_17, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_19;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_1 = x_13;
x_2 = x_20;
x_10 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__36(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_resolveNamespace___at_Lean_Elab_Term_elabOpen___spec__6(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__35(x_17, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_19;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openRenamingItem", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
x_4 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__3;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openSimple", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
x_4 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openScoped", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
x_4 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openOnly", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
x_4 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openHiding", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
x_4 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openRenaming", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1;
x_4 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__12() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_6, 7);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 6);
lean_inc(x_23);
x_24 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__1;
x_25 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__3;
lean_inc(x_1);
x_26 = l_Lean_Syntax_isOfKind(x_1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
if (x_26 == 0)
{
uint8_t x_260; 
x_260 = 0;
x_28 = x_260;
goto block_259;
}
else
{
uint8_t x_261; 
x_261 = 1;
x_28 = x_261;
goto block_259;
}
block_21:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
block_259:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_st_ref_get(x_7, x_8);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_mk_ref(x_27, x_30);
if (x_28 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__5;
lean_inc(x_1);
x_35 = l_Lean_Syntax_isOfKind(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__7;
lean_inc(x_1);
x_37 = l_Lean_Syntax_isOfKind(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__9;
lean_inc(x_1);
x_39 = l_Lean_Syntax_isOfKind(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__11;
lean_inc(x_1);
x_41 = l_Lean_Syntax_isOfKind(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___rarg(x_33);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
x_9 = x_42;
goto block_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_9 = x_46;
goto block_21;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Syntax_getArg(x_1, x_49);
lean_dec(x_1);
x_51 = l_Lean_Syntax_getArgs(x_50);
lean_dec(x_50);
x_52 = lean_array_get_size(x_51);
x_53 = lean_nat_dec_lt(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_103; 
lean_dec(x_52);
lean_dec(x_51);
x_103 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_54 = x_103;
goto block_102;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_52, x_52);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_52);
lean_dec(x_51);
x_105 = l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1;
x_54 = x_105;
goto block_102;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_108 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__12;
x_109 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_51, x_106, x_107, x_108);
lean_dec(x_51);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_54 = x_110;
goto block_102;
}
}
block_102:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__13;
x_56 = l_Array_sequenceMap___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__2(x_54, x_55);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_48);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___rarg(x_33);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
x_9 = x_57;
goto block_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_9 = x_61;
goto block_21;
}
}
else
{
lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_array_get_size(x_62);
x_64 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_65 = 0;
lean_inc(x_62);
x_66 = l_Array_mapMUnsafe_map___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__5(x_64, x_65, x_62);
x_67 = l_Array_mapMUnsafe_map___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__6(x_64, x_65, x_62);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_68 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5(x_48, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Array_zip___rarg(x_67, x_66);
lean_dec(x_66);
lean_dec(x_67);
x_72 = lean_array_get_size(x_71);
x_73 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_74 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_75 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__22(x_69, x_71, x_73, x_65, x_74, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_70);
lean_dec(x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
lean_inc(x_7);
lean_inc(x_32);
x_77 = lean_apply_9(x_24, x_74, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_get(x_7, x_79);
lean_dec(x_7);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_32, x_81);
lean_dec(x_32);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_82, 0, x_85);
x_9 = x_82;
goto block_21;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_82, 0);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_82);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_9 = x_89;
goto block_21;
}
}
else
{
uint8_t x_90; 
lean_dec(x_32);
lean_dec(x_7);
x_90 = !lean_is_exclusive(x_77);
if (x_90 == 0)
{
x_9 = x_77;
goto block_21;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_77, 0);
x_92 = lean_ctor_get(x_77, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_77);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_9 = x_93;
goto block_21;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
x_9 = x_75;
goto block_21;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_75, 0);
x_96 = lean_ctor_get(x_75, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_75);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_9 = x_97;
goto block_21;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_68);
if (x_98 == 0)
{
x_9 = x_68;
goto block_21;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_68, 0);
x_100 = lean_ctor_get(x_68, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_68);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_9 = x_101;
goto block_21;
}
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Lean_Syntax_getArg(x_1, x_111);
x_113 = lean_unsigned_to_nat(2u);
x_114 = l_Lean_Syntax_getArg(x_1, x_113);
lean_dec(x_1);
x_115 = l_Lean_Syntax_getArgs(x_114);
lean_dec(x_114);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_116 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5(x_112, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23(x_117, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_array_get_size(x_115);
x_122 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_123 = 0;
x_124 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
lean_inc(x_117);
x_125 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__25(x_117, x_115, x_122, x_123, x_124, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_120);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Array_mapMUnsafe_map___at_Lean_Elab_OpenDecl_elabOpenDecl___spec__35(x_122, x_123, x_115);
x_128 = lean_array_to_list(lean_box(0), x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_117);
lean_ctor_set(x_129, 1, x_128);
x_130 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(x_129, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_126);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_7);
lean_inc(x_32);
x_133 = lean_apply_9(x_24, x_131, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_st_ref_get(x_7, x_135);
lean_dec(x_7);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_st_ref_get(x_32, x_137);
lean_dec(x_32);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_138, 0, x_141);
x_9 = x_138;
goto block_21;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_9 = x_145;
goto block_21;
}
}
else
{
uint8_t x_146; 
lean_dec(x_32);
lean_dec(x_7);
x_146 = !lean_is_exclusive(x_133);
if (x_146 == 0)
{
x_9 = x_133;
goto block_21;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_133, 0);
x_148 = lean_ctor_get(x_133, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_133);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_9 = x_149;
goto block_21;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_125);
if (x_150 == 0)
{
x_9 = x_125;
goto block_21;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_125, 0);
x_152 = lean_ctor_get(x_125, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_125);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_9 = x_153;
goto block_21;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_115);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_116);
if (x_154 == 0)
{
x_9 = x_116;
goto block_21;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_116, 0);
x_156 = lean_ctor_get(x_116, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_116);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_9 = x_157;
goto block_21;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Lean_Syntax_getArg(x_1, x_158);
x_160 = lean_unsigned_to_nat(2u);
x_161 = l_Lean_Syntax_getArg(x_1, x_160);
lean_dec(x_1);
x_162 = l_Lean_Syntax_getArgs(x_161);
lean_dec(x_161);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_163 = l_Lean_resolveNamespace___at_Lean_Elab_Term_elabOpen___spec__6(x_159, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_array_get_size(x_162);
x_167 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_168 = 0;
x_169 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_170 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__32(x_164, x_162, x_167, x_168, x_169, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_165);
lean_dec(x_162);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
lean_inc(x_7);
lean_inc(x_32);
x_172 = lean_apply_9(x_24, x_169, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_st_ref_get(x_7, x_174);
lean_dec(x_7);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_st_ref_get(x_32, x_176);
lean_dec(x_32);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_177, 0, x_180);
x_9 = x_177;
goto block_21;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_177, 0);
x_182 = lean_ctor_get(x_177, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_177);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_173);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_9 = x_184;
goto block_21;
}
}
else
{
uint8_t x_185; 
lean_dec(x_32);
lean_dec(x_7);
x_185 = !lean_is_exclusive(x_172);
if (x_185 == 0)
{
x_9 = x_172;
goto block_21;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_172, 0);
x_187 = lean_ctor_get(x_172, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_172);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_9 = x_188;
goto block_21;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_170);
if (x_189 == 0)
{
x_9 = x_170;
goto block_21;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_170, 0);
x_191 = lean_ctor_get(x_170, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_170);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_9 = x_192;
goto block_21;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_162);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_193 = !lean_is_exclusive(x_163);
if (x_193 == 0)
{
x_9 = x_163;
goto block_21;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_163, 0);
x_195 = lean_ctor_get(x_163, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_163);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_9 = x_196;
goto block_21;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; size_t x_201; size_t x_202; lean_object* x_203; lean_object* x_204; 
x_197 = lean_unsigned_to_nat(1u);
x_198 = l_Lean_Syntax_getArg(x_1, x_197);
lean_dec(x_1);
x_199 = l_Lean_Syntax_getArgs(x_198);
lean_dec(x_198);
x_200 = lean_array_get_size(x_199);
x_201 = lean_usize_of_nat(x_200);
lean_dec(x_200);
x_202 = 0;
x_203 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__34(x_199, x_201, x_202, x_203, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_199);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_7);
lean_inc(x_32);
x_206 = lean_apply_9(x_24, x_203, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_st_ref_get(x_7, x_208);
lean_dec(x_7);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_st_ref_get(x_32, x_210);
lean_dec(x_32);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_211, 0, x_214);
x_9 = x_211;
goto block_21;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_211, 0);
x_216 = lean_ctor_get(x_211, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_211);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_9 = x_218;
goto block_21;
}
}
else
{
uint8_t x_219; 
lean_dec(x_32);
lean_dec(x_7);
x_219 = !lean_is_exclusive(x_206);
if (x_219 == 0)
{
x_9 = x_206;
goto block_21;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_206, 0);
x_221 = lean_ctor_get(x_206, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_206);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_9 = x_222;
goto block_21;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_204);
if (x_223 == 0)
{
x_9 = x_204;
goto block_21;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_204, 0);
x_225 = lean_ctor_get(x_204, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_204);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_9 = x_226;
goto block_21;
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; size_t x_233; size_t x_234; lean_object* x_235; lean_object* x_236; 
x_227 = lean_ctor_get(x_31, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_31, 1);
lean_inc(x_228);
lean_dec(x_31);
x_229 = lean_unsigned_to_nat(0u);
x_230 = l_Lean_Syntax_getArg(x_1, x_229);
lean_dec(x_1);
x_231 = l_Lean_Syntax_getArgs(x_230);
lean_dec(x_230);
x_232 = lean_array_get_size(x_231);
x_233 = lean_usize_of_nat(x_232);
lean_dec(x_232);
x_234 = 0;
x_235 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_227);
x_236 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__36(x_231, x_233, x_234, x_235, x_227, x_2, x_3, x_4, x_5, x_6, x_7, x_228);
lean_dec(x_231);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
lean_inc(x_7);
lean_inc(x_227);
x_238 = lean_apply_9(x_24, x_235, x_227, x_2, x_3, x_4, x_5, x_6, x_7, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_st_ref_get(x_7, x_240);
lean_dec(x_7);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_st_ref_get(x_227, x_242);
lean_dec(x_227);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_243, 0, x_246);
x_9 = x_243;
goto block_21;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_243, 0);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_243);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_239);
lean_ctor_set(x_249, 1, x_247);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_9 = x_250;
goto block_21;
}
}
else
{
uint8_t x_251; 
lean_dec(x_227);
lean_dec(x_7);
x_251 = !lean_is_exclusive(x_238);
if (x_251 == 0)
{
x_9 = x_238;
goto block_21;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_238, 0);
x_253 = lean_ctor_get(x_238, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_238);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_9 = x_254;
goto block_21;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_236);
if (x_255 == 0)
{
x_9 = x_236;
goto block_21;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_236, 0);
x_257 = lean_ctor_get(x_236, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_236);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_9 = x_258;
goto block_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__38(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_st_ref_take(x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 4);
lean_dec(x_20);
x_21 = l_Lean_ScopedEnvExtension_popScope___rarg(x_14, x_19);
lean_dec(x_14);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
lean_ctor_set(x_16, 4, x_22);
lean_ctor_set(x_16, 0, x_21);
x_23 = lean_st_ref_set(x_10, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_10, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
lean_ctor_set(x_28, 1, x_32);
x_33 = lean_st_ref_set(x_8, x_28, x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_37 = lean_box(0);
x_3 = x_36;
x_4 = x_37;
x_11 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 2);
x_41 = lean_ctor_get(x_28, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_st_ref_set(x_8, x_43, x_29);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_48 = lean_box(0);
x_3 = x_47;
x_4 = x_48;
x_11 = x_45;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
x_52 = lean_ctor_get(x_16, 2);
x_53 = lean_ctor_get(x_16, 3);
x_54 = lean_ctor_get(x_16, 5);
x_55 = lean_ctor_get(x_16, 6);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_56 = l_Lean_ScopedEnvExtension_popScope___rarg(x_14, x_50);
lean_dec(x_14);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4;
x_58 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set(x_58, 6, x_55);
x_59 = lean_st_ref_set(x_10, x_58, x_17);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_10, x_60);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_8, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 3);
lean_inc(x_68);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
x_70 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 4, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_68);
x_72 = lean_st_ref_set(x_8, x_71, x_65);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = 1;
x_75 = lean_usize_add(x_3, x_74);
x_76 = lean_box(0);
x_3 = x_75;
x_4 = x_76;
x_11 = x_73;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__38(x_12, x_15, x_16, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("open", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l_Lean_Elab_Term_elabOpen___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabOpen___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 10);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_25);
lean_ctor_set(x_32, 4, x_26);
lean_ctor_set(x_32, 5, x_27);
lean_ctor_set(x_32, 6, x_28);
lean_ctor_set(x_32, 7, x_20);
lean_ctor_set(x_32, 8, x_29);
lean_ctor_set(x_32, 9, x_30);
lean_ctor_set(x_32, 10, x_31);
x_33 = 1;
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Elab_Term_elabTerm(x_16, x_2, x_33, x_33, x_3, x_4, x_5, x_6, x_32, x_8, x_21);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37(x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37(x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_2);
x_49 = lean_ctor_get(x_19, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_dec(x_19);
x_51 = l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37(x_3, x_4, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabOpen___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_elabOpen___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_elabOpen___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabOpen___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabOpen___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Term_elabOpen___spec__14___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_elabOpen___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Term_elabOpen___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__22(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__24(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_activateScoped___at_Lean_Elab_Term_elabOpen___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__25(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getRefPos___at_Lean_Elab_Term_elabOpen___spec__30(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_elabOpen___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_elabOpen___spec__31(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__32(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__34(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_loop___at_Lean_Elab_Term_elabOpen___spec__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__36(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__38(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_popScope___at_Lean_Elab_Term_elabOpen___spec__37(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabOpen", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabOpen___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabOpen), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabOpen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabOpen___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(292u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(300u);
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__2;
x_4 = lean_unsigned_to_nat(12u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(292u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(292u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__5;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabOpen_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_KVMap_insertCore(x_11, x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type mismatch at set_option", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_DataValue_sameCtor(x_11, x_3);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__2;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___lambda__1(x_1, x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected set_option value ", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_7, 5);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getArgs(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Array_toSubarray___rarg(x_11, x_12, x_13);
x_15 = l_Array_ofSubarray___rarg(x_14);
lean_inc(x_10);
x_16 = l_Lean_Syntax_setArgs(x_10, x_15);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Term_addDotCompletionInfo___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Syntax_getId(x_1);
x_21 = lean_erase_macro_scopes(x_20);
lean_inc(x_21);
x_22 = l_Lean_getOptionDecl(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_inc(x_21);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Syntax_isStrLit_x3f(x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Syntax_isNatLit_x3f(x_2);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = l_Lean_Elab_Term_elabScientificLit___closed__9;
x_34 = lean_string_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Elab_Term_elabScientificLit___closed__6;
x_36 = lean_string_dec_eq(x_32, x_35);
lean_dec(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_23);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_2);
x_38 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_43 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__3;
x_44 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(x_21, x_23, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_2);
x_45 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__4;
x_46 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(x_21, x_23, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_23);
lean_dec(x_21);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_2);
x_48 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_Term_elabSyntheticHole___closed__8;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_53 = lean_ctor_get(x_31, 0);
lean_inc(x_53);
lean_dec(x_31);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(x_21, x_23, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
x_56 = lean_ctor_get(x_30, 0);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(x_21, x_23, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_22);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_22, 0);
x_61 = lean_io_error_to_string(x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_10);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_22, 0, x_64);
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_io_error_to_string(x_65);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_10);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_7, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_7, 2);
lean_dec(x_21);
x_22 = l_Lean_Elab_Term_elabSetOption___closed__1;
x_23 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_15, x_22);
lean_ctor_set(x_7, 4, x_23);
lean_ctor_set(x_7, 2, x_15);
x_24 = 1;
x_25 = l_Lean_Elab_Term_elabTerm(x_18, x_2, x_24, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 3);
x_29 = lean_ctor_get(x_7, 5);
x_30 = lean_ctor_get(x_7, 6);
x_31 = lean_ctor_get(x_7, 7);
x_32 = lean_ctor_get(x_7, 8);
x_33 = lean_ctor_get(x_7, 9);
x_34 = lean_ctor_get(x_7, 10);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_35 = l_Lean_Elab_Term_elabSetOption___closed__1;
x_36 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_15, x_35);
x_37 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set(x_37, 7, x_31);
lean_ctor_set(x_37, 8, x_32);
lean_ctor_set(x_37, 9, x_33);
lean_ctor_set(x_37, 10, x_34);
x_38 = 1;
x_39 = l_Lean_Elab_Term_elabTerm(x_18, x_2, x_38, x_38, x_3, x_4, x_5, x_6, x_37, x_8, x_16);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabSetOption___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabSetOption(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("set_option", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSetOption", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSetOption___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(302u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(305u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__2;
x_4 = lean_unsigned_to_nat(33u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(302u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(302u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__4;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__5;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = 0;
x_14 = l_Lean_Elab_Term_mkTermInfo(x_12, x_1, x_3, x_2, x_11, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWithAnnotateTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withAnnotateTerm", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l_Lean_Elab_Term_elabWithAnnotateTerm___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_box(x_17);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabWithAnnotateTerm___lambda__1___boxed), 10, 2);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_2);
x_22 = l_Lean_Elab_Term_withInfoContext_x27(x_14, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabWithAnnotateTerm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabWithAnnotateTerm___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabWithAnnotateTerm", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabWithAnnotateTerm), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(307u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(311u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(307u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(307u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__5;
x_4 = lean_unsigned_to_nat(62u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("System", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FilePath", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__1;
x_2 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__4;
x_10 = 1;
x_11 = l_Lean_Elab_Term_evalTerm___rarg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabIncludeStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("includeStr", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabIncludeStr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l_Lean_Elab_Term_elabIncludeStr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabIncludeStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cannot compute parent directory of '", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabIncludeStr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabIncludeStr___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabIncludeStr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabIncludeStr___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
x_20 = l_System_FilePath_parent(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_Term_elabIncludeStr___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_tryPostponeIfHasMVars___spec__1(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_System_FilePath_join(x_28, x_16);
x_30 = lean_st_ref_get(x_8, x_17);
lean_dec(x_8);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_IO_FS_readFile(x_29, x_31);
lean_dec(x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_mkStrLit(x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = l_Lean_mkStrLit(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_io_error_to_string(x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_32, 0, x_45);
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_io_error_to_string(x_46);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_15);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabIncludeStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabIncludeStr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabIncludeStr", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabIncludeStr___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__9;
x_3 = l_Lean_Elab_Term_elabIncludeStr___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(319u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(328u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__1;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__2;
x_4 = lean_unsigned_to_nat(34u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(319u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(319u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__4;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__5;
x_4 = lean_unsigned_to_nat(50u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Open(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SetOption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinTerm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Open(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SetOption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabProp___rarg___closed__1 = _init_l_Lean_Elab_Term_elabProp___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabProp___rarg___closed__1);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__1);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__2);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__3);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__4);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__5);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__6);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__7);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__8 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__8);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__9 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__9);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__10 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__10);
res = l___regBuiltin_Lean_Elab_Term_elabProp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabProp_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabSort___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSort___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort___closed__2);
l___regBuiltin_Lean_Elab_Term_elabSort___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort___closed__3);
l___regBuiltin_Lean_Elab_Term_elabSort___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort___closed__4);
l___regBuiltin_Lean_Elab_Term_elabSort___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabSort(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabSort_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2);
l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__3);
l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__4);
l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabTypeStx(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabTypeStx_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__1);
l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabPipeCompletion___lambda__1___closed__2);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__1);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__2);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__3);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__4);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabPipeCompletion_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__1);
l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__2);
l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__4);
l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabCompletion(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabCompletion_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabHole___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole___closed__1);
l___regBuiltin_Lean_Elab_Term_elabHole___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole___closed__2);
l___regBuiltin_Lean_Elab_Term_elabHole___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole___closed__3);
l___regBuiltin_Lean_Elab_Term_elabHole___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole___closed__4);
l___regBuiltin_Lean_Elab_Term_elabHole___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabHole_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1 = _init_l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_isWellFormed___at_Lean_Elab_Term_elabSyntheticHole___spec__3___closed__1);
l_Lean_Elab_Term_elabSyntheticHole___closed__1 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__1);
l_Lean_Elab_Term_elabSyntheticHole___closed__2 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__2);
l_Lean_Elab_Term_elabSyntheticHole___closed__3 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__3);
l_Lean_Elab_Term_elabSyntheticHole___closed__4 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__4);
l_Lean_Elab_Term_elabSyntheticHole___closed__5 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__5);
l_Lean_Elab_Term_elabSyntheticHole___closed__6 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__6);
l_Lean_Elab_Term_elabSyntheticHole___closed__7 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__7);
l_Lean_Elab_Term_elabSyntheticHole___closed__8 = _init_l_Lean_Elab_Term_elabSyntheticHole___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabSyntheticHole___closed__8);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__3);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__4);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabLetMVar___spec__1___rarg___closed__2);
l_Lean_Elab_Term_elabLetMVar___closed__1 = _init_l_Lean_Elab_Term_elabLetMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetMVar___closed__1);
l_Lean_Elab_Term_elabLetMVar___closed__2 = _init_l_Lean_Elab_Term_elabLetMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetMVar___closed__2);
l_Lean_Elab_Term_elabLetMVar___closed__3 = _init_l_Lean_Elab_Term_elabLetMVar___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetMVar___closed__3);
l_Lean_Elab_Term_elabLetMVar___closed__4 = _init_l_Lean_Elab_Term_elabLetMVar___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetMVar___closed__4);
l_Lean_Elab_Term_elabLetMVar___closed__5 = _init_l_Lean_Elab_Term_elabLetMVar___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetMVar___closed__5);
l_Lean_Elab_Term_elabLetMVar___closed__6 = _init_l_Lean_Elab_Term_elabLetMVar___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetMVar___closed__6);
l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabLetMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabLetMVar_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__1 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__1);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__2 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__2);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__3);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_getMVarFromUserName___closed__4);
l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1 = _init_l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1);
l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2 = _init_l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeMVar_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1 = _init_l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1);
l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2 = _init_l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabWaitIfTypeContainsMVar_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1 = _init_l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1);
l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2 = _init_l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabWaitIfContainsMVar_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabByTactic___closed__1 = _init_l_Lean_Elab_Term_elabByTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabByTactic___closed__1);
l_Lean_Elab_Term_elabByTactic___closed__2 = _init_l_Lean_Elab_Term_elabByTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabByTactic___closed__2);
l_Lean_Elab_Term_elabByTactic___closed__3 = _init_l_Lean_Elab_Term_elabByTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabByTactic___closed__3);
l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1);
l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2);
l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__3);
l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__4);
l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabByTactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabByTactic_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__3);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__4);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabNoImplicitLambda_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabBadCDot___rarg___closed__1 = _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___rarg___closed__1);
l_Lean_Elab_Term_elabBadCDot___rarg___closed__2 = _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___rarg___closed__2);
l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1);
l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__2);
l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__3);
l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__4);
l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabBadCDot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabBadCDot_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__1);
l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2 = _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Term_elabStrLit___spec__1___closed__2);
l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__1);
l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__2);
l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__4);
l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabStrLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabStrLit_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNumLit___lambda__1___closed__1);
l_Lean_Elab_Term_elabNumLit___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNumLit___lambda__1___closed__2);
l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabNumLit___lambda__1___closed__3);
l_Lean_Elab_Term_elabNumLit___lambda__1___closed__4 = _init_l_Lean_Elab_Term_elabNumLit___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabNumLit___lambda__1___closed__4);
l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__4);
l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabNumLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabNumLit_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__1);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__2);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__4);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabRawNatLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabRawNatLit_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabScientificLit___closed__1 = _init_l_Lean_Elab_Term_elabScientificLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__1);
l_Lean_Elab_Term_elabScientificLit___closed__2 = _init_l_Lean_Elab_Term_elabScientificLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__2);
l_Lean_Elab_Term_elabScientificLit___closed__3 = _init_l_Lean_Elab_Term_elabScientificLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__3);
l_Lean_Elab_Term_elabScientificLit___closed__4 = _init_l_Lean_Elab_Term_elabScientificLit___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__4);
l_Lean_Elab_Term_elabScientificLit___closed__5 = _init_l_Lean_Elab_Term_elabScientificLit___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__5);
l_Lean_Elab_Term_elabScientificLit___closed__6 = _init_l_Lean_Elab_Term_elabScientificLit___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__6);
l_Lean_Elab_Term_elabScientificLit___closed__7 = _init_l_Lean_Elab_Term_elabScientificLit___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__7);
l_Lean_Elab_Term_elabScientificLit___closed__8 = _init_l_Lean_Elab_Term_elabScientificLit___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__8);
l_Lean_Elab_Term_elabScientificLit___closed__9 = _init_l_Lean_Elab_Term_elabScientificLit___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__9);
l_Lean_Elab_Term_elabScientificLit___closed__10 = _init_l_Lean_Elab_Term_elabScientificLit___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__10);
l_Lean_Elab_Term_elabScientificLit___closed__11 = _init_l_Lean_Elab_Term_elabScientificLit___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabScientificLit___closed__11);
l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__1);
l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__2);
l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__4);
l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabScientificLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabScientificLit_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabCharLit___closed__1 = _init_l_Lean_Elab_Term_elabCharLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabCharLit___closed__1);
l_Lean_Elab_Term_elabCharLit___closed__2 = _init_l_Lean_Elab_Term_elabCharLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabCharLit___closed__2);
l_Lean_Elab_Term_elabCharLit___closed__3 = _init_l_Lean_Elab_Term_elabCharLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabCharLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__1);
l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__2);
l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__4);
l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabCharLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabCharLit_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1);
l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2);
l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__3);
l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__4);
l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabQuotedName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabQuotedName_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Term_elabDoubleQuotedName___spec__6___closed__2);
l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__1);
l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__2 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__2);
l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Term_elabDoubleQuotedName___spec__3___closed__3);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__1);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Term_elabDoubleQuotedName___spec__2___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__3);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__4);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabDoubleQuotedName_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabDeclName___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDeclName___lambda__1___closed__1);
l_Lean_Elab_Term_elabDeclName___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabDeclName___lambda__1___closed__2);
l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabDeclName___lambda__1___closed__3);
l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4 = _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabDeclName___lambda__1___closed__4);
l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5 = _init_l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabDeclName___lambda__1___closed__5);
l_Lean_Elab_Term_elabDeclName___closed__1 = _init_l_Lean_Elab_Term_elabDeclName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDeclName___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__3);
l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__4);
l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabDeclName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabDeclName_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__3);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__4);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabWithDeclName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabWithDeclName_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2);
l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__3);
l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__4);
l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabTypeOf(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabTypeOf_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__1 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__1);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_mkSilentAnnotationIfHole___closed__2);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__1);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__3);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__4);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__1);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__2);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__3);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__4);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabEnsureExpectedType_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabClear___spec__4___closed__3);
l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___closed__1 = _init_l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___closed__1();
lean_mark_persistent(l_Lean_exprDependsOn___at_Lean_Elab_Term_elabClear___spec__7___closed__1);
l_Lean_Elab_Term_elabClear___lambda__2___closed__1 = _init_l_Lean_Elab_Term_elabClear___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabClear___lambda__2___closed__1);
l_Lean_Elab_Term_elabClear___lambda__2___closed__2 = _init_l_Lean_Elab_Term_elabClear___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabClear___lambda__2___closed__2);
l_Lean_Elab_Term_elabClear___closed__1 = _init_l_Lean_Elab_Term_elabClear___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabClear___closed__1);
l_Lean_Elab_Term_elabClear___closed__2 = _init_l_Lean_Elab_Term_elabClear___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabClear___closed__2);
l___regBuiltin_Lean_Elab_Term_elabClear___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear___closed__1);
l___regBuiltin_Lean_Elab_Term_elabClear___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear___closed__2);
l___regBuiltin_Lean_Elab_Term_elabClear___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear___closed__3);
l___regBuiltin_Lean_Elab_Term_elabClear___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear___closed__4);
l___regBuiltin_Lean_Elab_Term_elabClear___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabClear___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabClear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabClear_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabClear_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_elabOpen___spec__2___closed__12);
l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1 = _init_l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1();
lean_mark_persistent(l_Lean_pushScope___at_Lean_Elab_Term_elabOpen___spec__1___closed__1);
l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1 = _init_l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1();
lean_mark_persistent(l_Lean_resolveNamespaceCore___at_Lean_Elab_Term_elabOpen___spec__9___closed__1);
l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1 = _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__1);
l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2 = _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___at_Lean_Elab_Term_elabOpen___spec__5___closed__2);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__1 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__1();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__1);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__2);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__3 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__3();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__3);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Term_elabOpen___spec__29___closed__4);
l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__1 = _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__1();
lean_mark_persistent(l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__1);
l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__2 = _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__2();
lean_mark_persistent(l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Term_elabOpen___spec__28___closed__2);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__1 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__1);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__2 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___lambda__1___closed__2);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__1 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__1);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__2 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__2);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__3 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__3);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Term_elabOpen___spec__26___closed__4);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__1);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__2 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__2);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__3 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___lambda__2___closed__3);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__1 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__1);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__2 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__2);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__3 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__3();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__3);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__4 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__4();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__4);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__5 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__5();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__5);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__6 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__6();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__6);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__7 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__7();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__7);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__8 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__8();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__8);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__9 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__9();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__9);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__10 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__10();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__10);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__11 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__11();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__11);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__12 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__12();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__12);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__13 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__13();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Term_elabOpen___spec__3___closed__13);
l_Lean_Elab_Term_elabOpen___closed__1 = _init_l_Lean_Elab_Term_elabOpen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabOpen___closed__1);
l_Lean_Elab_Term_elabOpen___closed__2 = _init_l_Lean_Elab_Term_elabOpen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabOpen___closed__2);
l___regBuiltin_Lean_Elab_Term_elabOpen___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen___closed__1);
l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen___closed__2);
l___regBuiltin_Lean_Elab_Term_elabOpen___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabOpen_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabOpen_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__1 = _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__1);
l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__2 = _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Term_elabSetOption___spec__3___closed__2);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__1 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__1);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__2);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__3 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__3);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__4 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Term_elabSetOption___spec__1___closed__4);
l_Lean_Elab_Term_elabSetOption___closed__1 = _init_l_Lean_Elab_Term_elabSetOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabSetOption___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__2);
l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__3);
l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__4);
l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabSetOption_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabWithAnnotateTerm___closed__1 = _init_l_Lean_Elab_Term_elabWithAnnotateTerm___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabWithAnnotateTerm___closed__1);
l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2 = _init_l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabWithAnnotateTerm___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabWithAnnotateTerm_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__1 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__1);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__2 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__2);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__3 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__3);
l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__4 = _init_l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinTerm_0__Lean_Elab_Term_evalFilePathUnsafe___closed__4);
l_Lean_Elab_Term_elabIncludeStr___closed__1 = _init_l_Lean_Elab_Term_elabIncludeStr___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabIncludeStr___closed__1);
l_Lean_Elab_Term_elabIncludeStr___closed__2 = _init_l_Lean_Elab_Term_elabIncludeStr___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabIncludeStr___closed__2);
l_Lean_Elab_Term_elabIncludeStr___closed__3 = _init_l_Lean_Elab_Term_elabIncludeStr___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabIncludeStr___closed__3);
l_Lean_Elab_Term_elabIncludeStr___closed__4 = _init_l_Lean_Elab_Term_elabIncludeStr___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabIncludeStr___closed__4);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__1);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__2);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabIncludeStr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_elabIncludeStr_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
