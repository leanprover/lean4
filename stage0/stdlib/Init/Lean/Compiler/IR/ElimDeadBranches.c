// Lean compiler output
// Module: Init.Lean.Compiler.IR.ElimDeadBranches
// Imports: Init.Control.Reader Init.Data.Option Init.Data.Nat Init.Lean.Compiler.IR.Format Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.CompilerM
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
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3;
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findArgValue(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(lean_object*, uint8_t, lean_object*);
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5;
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_List_format___rarg___closed__4;
lean_object* l_Array_getD___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_Value_beq___main(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8;
lean_object* l_Lean_IR_UnreachableBranches_Value_merge(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_fmt___at_Lean_IR_UnreachableBranches_Value_format___main___spec__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___rarg(lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_inferMain___boxed(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6;
lean_object* l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_HasBeq;
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__19(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_projValue(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
uint8_t l_Array_isEqvAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main(lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(lean_object*, size_t, size_t);
extern lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2(lean_object*);
extern lean_object* l_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__20(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___main___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14;
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_Monad;
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_Value_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2___boxed(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__6(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_addFunctionSummary(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(lean_object*, uint8_t, lean_object*);
extern lean_object* l_PersistentArrayNode_Inhabited___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_widening(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_updateCurrFnSummary(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findVarValue(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_Inhabited;
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_projValue___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1___boxed(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findArgValue___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_elimDead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__7;
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__3;
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2(lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_merge___main(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7;
lean_object* l_Lean_IR_UnreachableBranches_Value_HasToString;
lean_object* l_Lean_IR_UnreachableBranches_projValue___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_containsCtor(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___boxed(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Decl_Inhabited;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_List_format___at_Lean_IR_UnreachableBranches_Value_format___main___spec__4(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__6(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__1;
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__13(lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2___boxed(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2(lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_projValue___main(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_containsCtor___main(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__1;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3;
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferStep(lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__10(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_elimDeadBranches___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12;
lean_object* l_Lean_IR_UnreachableBranches_elimDead(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__18(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary___boxed(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2;
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1;
lean_object* l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpExpr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__5;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat;
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4(lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_regNamespacesExtension___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1;
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findVarValue___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2;
lean_object* l_mkPersistentArray___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9;
lean_object* l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(lean_object*, lean_object*);
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
lean_object* _init_l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___main___boxed), 2, 0);
return x_1;
}
}
uint8_t l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean_box(0), x_7, x_8);
return x_9;
}
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(x_1, x_2, x_5);
x_7 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(x_1, x_2, x_5);
x_7 = 0;
x_8 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(x_4, x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_6;
}
}
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(x_1, x_2, x_5);
x_7 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_4, x_1);
if (x_7 == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(x_1, x_2, x_5);
x_7 = 0;
x_8 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(x_4, x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_6;
}
}
}
}
uint8_t l_Lean_IR_UnreachableBranches_Value_beq___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_IR_CtorInfo_beq(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(x_8, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_2, 0);
x_17 = 1;
x_18 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(x_16, x_17, x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(x_15, x_17, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
}
lean_object* l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_UnreachableBranches_Value_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad;
x_2 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Compiler.IR.ElimDeadBranches");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid addChoice");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2;
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = l_Lean_IR_CtorInfo_beq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_1, x_7, x_3);
lean_ctor_set(x_2, 1, x_14);
return x_2;
}
else
{
lean_object* x_15; 
x_15 = lean_apply_2(x_1, x_5, x_3);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = l_Lean_IR_CtorInfo_beq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = 1;
x_21 = l_Bool_DecidableEq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_1, x_16, x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_apply_2(x_1, x_5, x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1;
x_27 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4;
x_28 = lean_panic_fn(x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1;
x_30 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4;
x_31 = lean_panic_fn(x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = lean_array_get(x_11, x_2, x_10);
lean_dec(x_10);
x_14 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_12, x_13);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
lean_object* _init_l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge___main), 2, 0);
return x_1;
}
}
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_6 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_5, x_1, x_3);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_merge___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_IR_CtorInfo_beq(x_3, x_5);
lean_dec(x_5);
x_8 = 1;
x_9 = l_Bool_DecidableEq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_array_get_size(x_4);
x_18 = l_Array_empty___closed__1;
lean_inc(x_17);
x_19 = l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(x_4, x_6, x_17, x_17, x_18);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_20 = lean_array_get_size(x_4);
x_21 = l_Array_empty___closed__1;
lean_inc(x_20);
x_22 = l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(x_4, x_6, x_20, x_20, x_21);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
default: 
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_27 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_26, x_25, x_1);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_30 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_29, x_28, x_1);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_35 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_34, x_33, x_2);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_38 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_37, x_36, x_2);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
default: 
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(x_42, x_40);
lean_ctor_set(x_2, 0, x_43);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(x_44, x_40);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_IR_UnreachableBranches_Value_format___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l_Lean_IR_UnreachableBranches_Value_format___main(x_7);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_IR_UnreachableBranches_Value_format___main(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_IR_UnreachableBranches_Value_format___main(x_7);
x_9 = 0;
lean_inc(x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(x_4, x_2);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_9);
return x_12;
}
}
}
}
lean_object* l_Lean_List_format___at_Lean_IR_UnreachableBranches_Value_format___main___spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_List_format___rarg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_List_format___rarg___closed__4;
x_4 = l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(x_1, x_3);
x_5 = 0;
x_6 = l_Lean_Format_sbracket___closed__2;
x_7 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
x_8 = l_Lean_Format_sbracket___closed__3;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_5);
x_10 = l_Lean_Format_sbracket___closed__1;
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_format_group(x_11);
return x_12;
}
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bot");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("top");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Array_isEmpty___rarg(x_5);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_box(0);
x_13 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(x_5, x_5, x_11, x_12);
lean_dec(x_5);
x_14 = 0;
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = l_Lean_Format_paren___closed__2;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_14);
x_18 = l_Lean_Format_paren___closed__3;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_14);
x_20 = l_Lean_Format_paren___closed__1;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_format_group(x_21);
x_23 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__5;
x_24 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_25);
x_27 = 0;
x_28 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__5;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_27);
return x_29;
}
}
default: 
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_List_format___at_Lean_IR_UnreachableBranches_Value_format___main___spec__4(x_30);
x_32 = 0;
x_33 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__7;
x_34 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_32);
return x_34;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_Value_format___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_format), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_4;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_fget(x_4, x_3);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = x_10;
x_12 = lean_array_fset(x_4, x_3, x_11);
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_1);
x_13 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_9, x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
x_16 = x_13;
x_17 = lean_array_fset(x_12, x_3, x_16);
lean_dec(x_3);
x_3 = x_15;
x_4 = x_17;
goto _start;
}
}
}
lean_object* l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_6, x_2);
x_9 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_10, x_2);
x_13 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
uint8_t l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_Lean_Name_getPrefix(x_7);
lean_dec(x_7);
x_9 = l_Lean_NameSet_contains(x_3, x_8);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc(x_1);
x_12 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_3, x_13, x_6);
lean_ctor_set(x_2, 1, x_14);
return x_2;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 5)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*5);
lean_dec(x_16);
x_18 = l_Bool_DecidableEq(x_17, x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_3, x_19, x_6);
lean_ctor_set(x_2, 1, x_20);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_box(0);
x_22 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_8, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_22, x_23, x_6);
lean_ctor_set(x_2, 1, x_24);
return x_2;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_8);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_3, x_25, x_6);
lean_ctor_set(x_2, 1, x_26);
return x_2;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_8);
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(1);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = l_Lean_Name_getPrefix(x_30);
lean_dec(x_30);
x_32 = l_Lean_NameSet_contains(x_3, x_31);
x_33 = 1;
x_34 = l_Bool_DecidableEq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_31);
lean_inc(x_1);
x_35 = lean_environment_find(x_1, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_3, x_36, x_29);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
if (lean_obj_tag(x_39) == 5)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*5);
lean_dec(x_40);
x_42 = l_Bool_DecidableEq(x_41, x_33);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_3, x_43, x_29);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_box(0);
x_47 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_31, x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_47, x_48, x_29);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_31);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_3, x_51, x_29);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_box(1);
return x_54;
}
}
}
case 3:
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_3, x_56);
x_58 = lean_box(1);
x_59 = l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(x_58, x_57);
x_60 = 1;
x_61 = l_Bool_DecidableEq(x_59, x_60);
if (x_61 == 0)
{
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
else
{
lean_object* x_62; 
lean_dec(x_57);
lean_free_object(x_2);
x_62 = lean_box(1);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
lean_dec(x_2);
x_64 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_3, x_63);
x_65 = lean_box(1);
x_66 = l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(x_65, x_64);
x_67 = 1;
x_68 = l_Bool_DecidableEq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_64);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_64);
x_70 = lean_box(1);
return x_70;
}
}
}
default: 
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_widening(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = lean_array_fset(x_5, x_2, x_3);
x_30 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
x_22 = 1;
x_23 = l_Bool_DecidableEq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
x_24 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_fset(x_17, x_12, x_25);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_27 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
x_31 = 1;
x_32 = l_Bool_DecidableEq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_PersistentHashMap_mkCollisionNode___rarg(x_28, x_29, x_4, x_5);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_array_fset(x_17, x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
x_37 = lean_array_fset(x_17, x_12, x_36);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = x_2 >> x_9;
x_41 = x_3 + x_8;
x_42 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_39, x_40, x_41, x_4, x_5);
lean_ctor_set(x_15, 0, x_42);
x_43 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_43);
return x_1;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = x_2 >> x_9;
x_46 = x_3 + x_8;
x_47 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_44, x_45, x_46, x_4, x_5);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
default: 
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_5);
x_51 = lean_array_fset(x_17, x_12, x_50);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
}
}
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = 1;
x_54 = 5;
x_55 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_56 = x_2 & x_55;
x_57 = lean_usize_to_nat(x_56);
x_58 = lean_array_get_size(x_52);
x_59 = lean_nat_dec_lt(x_57, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_52);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_array_fget(x_52, x_57);
x_62 = lean_box(2);
x_63 = lean_array_fset(x_52, x_57, x_62);
switch (lean_obj_tag(x_61)) {
case 0:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
x_67 = lean_name_eq(x_4, x_64);
x_68 = 1;
x_69 = l_Bool_DecidableEq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
x_70 = l_PersistentHashMap_mkCollisionNode___rarg(x_64, x_65, x_4, x_5);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_array_fset(x_63, x_57, x_71);
lean_dec(x_57);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_65);
lean_dec(x_64);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_66;
}
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_5);
x_75 = lean_array_fset(x_63, x_57, x_74);
lean_dec(x_57);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
case 1:
{
lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_61, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
x_79 = x_2 >> x_54;
x_80 = x_3 + x_53;
x_81 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_77, x_79, x_80, x_4, x_5);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_array_fset(x_63, x_57, x_82);
lean_dec(x_57);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_5);
x_86 = lean_array_fset(x_63, x_57, x_85);
lean_dec(x_57);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; size_t x_98; uint8_t x_99; 
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__4(x_1, x_88, x_4, x_5);
x_98 = 7;
x_99 = x_98 <= x_3;
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_89);
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_nat_dec_lt(x_100, x_101);
lean_dec(x_100);
x_90 = x_102;
goto block_97;
}
else
{
uint8_t x_103; 
x_103 = 1;
x_90 = x_103;
goto block_97;
}
block_97:
{
uint8_t x_91; uint8_t x_92; 
x_91 = 1;
x_92 = l_Bool_DecidableEq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_96 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(x_3, x_93, x_94, x_93, x_88, x_95);
lean_dec(x_94);
lean_dec(x_93);
return x_96;
}
else
{
return x_89;
}
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__10(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(x_2, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_array_uset(x_6, x_9, x_16);
x_18 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash(x_2);
x_26 = lean_usize_modn(x_25, x_24);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(x_2, x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_27);
x_34 = lean_array_uset(x_23, x_26, x_33);
x_35 = lean_nat_dec_le(x_32, x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(x_32, x_34);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(x_4, x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(x_7, x_7, x_8, x_4);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_SMap_switch___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__18(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_2, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_10);
return x_1;
}
else
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = 0;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
return x_12;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = 1;
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Bool_DecidableEq(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_3);
x_11 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_12 = lean_io_ref_get(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
lean_dec(x_13);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_io_ref_get(x_11, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_ref_reset(x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_17);
x_24 = x_17;
x_25 = lean_array_push(x_19, x_24);
x_26 = lean_io_ref_set(x_11, x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
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
lean_dec(x_19);
lean_dec(x_17);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_dec(x_17);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
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
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
x_49 = 1;
x_50 = lean_unbox(x_47);
lean_dec(x_47);
x_51 = l_Bool_DecidableEq(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_55 = lean_io_ref_get(x_54, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_get_size(x_56);
lean_dec(x_56);
x_59 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2;
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_1);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_io_ref_get(x_54, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_io_ref_reset(x_54, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_60);
x_67 = x_60;
x_68 = lean_array_push(x_62, x_67);
x_69 = lean_io_ref_set(x_54, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_60);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_60);
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_79 = x_64;
} else {
 lean_dec_ref(x_64);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_60);
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_83 = x_61;
} else {
 lean_dec_ref(x_61);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_85 = lean_ctor_get(x_55, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_87 = x_55;
} else {
 lean_dec_ref(x_55);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
return x_3;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_3, 0);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_3);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = 1;
x_12 = l_Bool_DecidableEq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = l_Array_empty___closed__1;
lean_inc(x_13);
x_15 = lean_apply_1(x_13, x_14);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(x_17, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 4);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_io_ref_get(x_3, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_io_ref_reset(x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_25);
x_32 = x_25;
x_33 = lean_array_push(x_27, x_32);
x_34 = lean_io_ref_set(x_3, x_33, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_25);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
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
lean_dec(x_27);
lean_dec(x_25);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
return x_29;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_29, 0);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_29);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_25);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_13);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l_System_FilePath_dirName___closed__1;
x_57 = l_Lean_Name_toStringWithSep___main(x_56, x_55);
x_58 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_61 = lean_string_append(x_59, x_60);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_61);
return x_4;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_4, 0);
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_4);
x_64 = lean_array_get_size(x_62);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(x_1, x_62, x_62, x_64, x_65);
lean_dec(x_64);
lean_dec(x_62);
x_67 = 1;
x_68 = l_Bool_DecidableEq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = l_Array_empty___closed__1;
lean_inc(x_69);
x_71 = lean_apply_1(x_69, x_70);
x_72 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_73 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_73, 0, x_71);
lean_closure_set(x_73, 1, x_72);
x_74 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(x_73, x_63);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 4);
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_69);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set(x_81, 5, x_80);
x_82 = lean_io_ref_get(x_3, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_io_ref_reset(x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_81);
x_88 = x_81;
x_89 = lean_array_push(x_83, x_88);
x_90 = lean_io_ref_set(x_3, x_89, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
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
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_81);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_83);
lean_dec(x_81);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_100 = x_85;
} else {
 lean_dec_ref(x_85);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_81);
x_102 = lean_ctor_get(x_82, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_82, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_104 = x_82;
} else {
 lean_dec_ref(x_82);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_69);
lean_dec(x_1);
x_106 = lean_ctor_get(x_74, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_74, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_108 = x_74;
} else {
 lean_dec_ref(x_74);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
lean_dec(x_1);
x_111 = l_System_FilePath_dirName___closed__1;
x_112 = l_Lean_Name_toStringWithSep___main(x_111, x_110);
x_113 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_63);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__19(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
x_9 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__20(x_8, x_2);
return x_9;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12;
x_4 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(x_1, x_1, x_2, x_3);
x_5 = l_Lean_SMap_switch___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__18(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachBranchesFunSummary");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2;
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3;
x_3 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4;
x_4 = l_Lean_regNamespacesExtension___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__19(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_HashMap_Inhabited___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4;
x_2 = lean_box(0);
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5;
x_4 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6;
x_5 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7;
x_6 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_addFunctionSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Bool_DecidableEq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
}
case 1:
{
lean_object* x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = x_2 >> x_5;
x_20 = l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3(x_18, x_19, x_3);
lean_dec(x_18);
return x_20;
}
default: 
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__4(x_22, x_23, lean_box(0), x_24, x_3);
return x_25;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_PersistentHashMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5(x_8, x_2);
return x_9;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = l_Lean_SMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__1(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find___at_Lean_IR_UnreachableBranches_getFunctionSummary___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_getFunctionSummary(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_IR_UnreachableBranches_findVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_HashMap_Inhabited___closed__1;
x_7 = lean_array_get(x_6, x_4, x_5);
lean_dec(x_4);
x_8 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_findVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_findVarValue(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_findArgValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_UnreachableBranches_findVarValue(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_findArgValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_findArgValue(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(x_2, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_array_uset(x_6, x_9, x_16);
x_18 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_2);
x_26 = lean_usize_modn(x_25, x_24);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(x_2, x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_27);
x_34 = lean_array_uset(x_23, x_26, x_33);
x_35 = lean_nat_dec_le(x_32, x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(x_32, x_34);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_UnreachableBranches_findVarValue(x_1, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_fget(x_10, x_11);
x_16 = l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
x_17 = lean_array_fset(x_10, x_11, x_16);
x_18 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_9);
x_19 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_15, x_1, x_18);
x_20 = lean_array_fset(x_17, x_11, x_19);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_box(0);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_array_get_size(x_23);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_box(0);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_array_fget(x_23, x_25);
x_31 = l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
x_32 = lean_array_fset(x_23, x_25, x_31);
x_33 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_22);
x_34 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_30, x_1, x_33);
x_35 = lean_array_fset(x_32, x_25, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
x_37 = lean_box(0);
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_37);
return x_5;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_5, 1);
x_39 = lean_ctor_get(x_5, 0);
lean_inc(x_38);
lean_inc(x_39);
lean_dec(x_5);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_array_get_size(x_40);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_array_fget(x_40, x_43);
x_50 = l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
x_51 = lean_array_fset(x_40, x_43, x_50);
x_52 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_39);
x_53 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_49, x_1, x_52);
x_54 = lean_array_fset(x_51, x_43, x_53);
if (lean_is_scalar(x_42)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_42;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_41);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_IR_UnreachableBranches_projValue___main(x_4, x_1);
x_7 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_box(0);
x_5 = l_Array_getD___rarg(x_3, x_2, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_box(0);
x_8 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(x_2, x_7, x_6);
return x_8;
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = l_Lean_IR_UnreachableBranches_findArgValue(x_10, x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_13, x_1, x_19);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_20;
x_4 = x_16;
goto _start;
}
}
}
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_Decl_name(x_7);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
}
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_PersistentArray_getAux___main___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_usize_to_nat(x_2);
x_18 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_19 = lean_array_get(x_18, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_usize_of_nat(x_2);
x_7 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_8 = l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_11 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_12 = lean_array_get(x_11, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(x_6, x_5, x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_IR_UnreachableBranches_findVarValue(x_16, x_2, x_3);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_IR_UnreachableBranches_projValue___main(x_19, x_15);
lean_dec(x_15);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l_Lean_IR_UnreachableBranches_projValue___main(x_21, x_15);
lean_dec(x_15);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = l_Lean_IR_UnreachableBranches_getFunctionSummary(x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(x_25, x_28, x_29);
lean_dec(x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_34, x_33);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
}
default: 
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_box(1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_interpExpr(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(x_1, x_2, x_5);
x_7 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_4, x_1);
if (x_7 == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_Lean_IR_UnreachableBranches_containsCtor___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
case 2:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_IR_CtorInfo_beq(x_5, x_2);
return x_6;
}
default: 
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 0;
x_9 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(x_2, x_8, x_7);
return x_9;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_UnreachableBranches_containsCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = x_4 >> x_5;
x_9 = 1;
x_10 = x_9 << x_5;
x_11 = x_10 - x_9;
x_12 = x_4 & x_11;
x_13 = 5;
x_14 = x_5 - x_13;
x_15 = lean_usize_to_nat(x_8);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_7, x_15);
x_19 = l_PersistentArrayNode_Inhabited___closed__1;
x_20 = lean_array_fset(x_7, x_15, x_19);
x_21 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_18, x_12, x_14);
x_22 = lean_array_fset(x_20, x_15, x_21);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = x_4 >> x_5;
x_25 = 1;
x_26 = x_25 << x_5;
x_27 = x_26 - x_25;
x_28 = x_4 & x_27;
x_29 = 5;
x_30 = x_5 - x_29;
x_31 = lean_usize_to_nat(x_24);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = l_PersistentArrayNode_Inhabited___closed__1;
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_35, x_28, x_30);
x_39 = lean_array_fset(x_37, x_31, x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_usize_to_nat(x_4);
x_44 = lean_array_get_size(x_42);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_array_fget(x_42, x_43);
x_47 = lean_box(1);
x_48 = lean_array_fset(x_42, x_43, x_47);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_IR_UnreachableBranches_Value_widening(x_49, x_1, x_46);
x_51 = lean_array_fset(x_48, x_43, x_50);
lean_dec(x_43);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_usize_to_nat(x_4);
x_54 = lean_array_get_size(x_52);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_array_fget(x_52, x_53);
x_58 = lean_box(1);
x_59 = lean_array_fset(x_52, x_53, x_58);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_dec(x_2);
x_61 = l_Lean_IR_UnreachableBranches_Value_widening(x_60, x_1, x_57);
x_62 = lean_array_fset(x_59, x_53, x_61);
lean_dec(x_53);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_4);
x_12 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(1);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_IR_UnreachableBranches_Value_widening(x_19, x_1, x_16);
x_21 = lean_array_fset(x_18, x_13, x_20);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_21);
return x_3;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get_usize(x_3, 4);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_27 = lean_nat_dec_le(x_26, x_4);
if (x_27 == 0)
{
size_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_4);
x_29 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_22, x_28, x_25);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set_usize(x_30, 4, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_nat_sub(x_4, x_26);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set_usize(x_34, 4, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = lean_box(1);
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lean_IR_UnreachableBranches_Value_widening(x_38, x_1, x_35);
x_40 = lean_array_fset(x_37, x_31, x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_24);
lean_ctor_set(x_41, 3, x_26);
lean_ctor_set_usize(x_41, 4, x_25);
return x_41;
}
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateCurrFnSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(x_1, x_2, x_6, x_4);
lean_dec(x_4);
lean_ctor_set(x_3, 1, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(x_1, x_2, x_11, x_4);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_nat_sub(x_4, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Lean_IR_paramInh;
x_16 = lean_array_get(x_15, x_1, x_14);
x_17 = l_Lean_IR_Arg_Inhabited;
x_18 = lean_array_get(x_17, x_2, x_14);
lean_dec(x_14);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_IR_UnreachableBranches_findVarValue(x_19, x_7, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_IR_UnreachableBranches_findArgValue(x_18, x_7, x_22);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_21);
x_26 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_21, x_24);
x_27 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_26, x_21);
lean_dec(x_21);
x_28 = 1;
x_29 = l_Bool_DecidableEq(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_array_get_size(x_31);
x_33 = lean_nat_dec_lt(x_3, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_26);
lean_dec(x_19);
x_5 = x_12;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_array_fget(x_31, x_3);
x_36 = l_HashMap_Inhabited___closed__1;
x_37 = lean_array_fset(x_31, x_3, x_36);
x_38 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_35, x_19, x_26);
x_39 = lean_array_fset(x_37, x_3, x_38);
lean_ctor_set(x_25, 0, x_39);
x_5 = x_12;
x_6 = x_28;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_array_get_size(x_41);
x_44 = lean_nat_dec_lt(x_3, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_26);
lean_dec(x_19);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
x_5 = x_12;
x_6 = x_28;
x_8 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_array_fget(x_41, x_3);
x_48 = l_HashMap_Inhabited___closed__1;
x_49 = lean_array_fset(x_41, x_3, x_48);
x_50 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_47, x_19, x_26);
x_51 = lean_array_fset(x_49, x_3, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
x_5 = x_12;
x_6 = x_28;
x_8 = x_52;
goto _start;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_19);
x_5 = x_12;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_5);
x_55 = lean_box(x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
return x_56;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_array_get_size(x_1);
x_7 = 0;
lean_inc(x_6);
x_8 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(x_1, x_2, x_5, x_6, x_6, x_7, x_3, x_4);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_1, x_13);
lean_dec(x_13);
x_16 = 1;
x_17 = l_Bool_DecidableEq(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_14);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_4);
x_19 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_14, x_4, x_5);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_3 = x_12;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
lean_inc(x_4);
x_23 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_22, x_4, x_5);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_3 = x_12;
x_5 = x_24;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_IR_UnreachableBranches_interpExpr(x_14, x_2, x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_13, x_17, x_2, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_15;
x_3 = x_20;
goto _start;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 3);
x_28 = l_Lean_IR_LocalContext_addJP(x_27, x_22, x_23, x_24);
lean_ctor_set(x_2, 3, x_28);
x_1 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
x_33 = lean_ctor_get(x_2, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_34 = l_Lean_IR_LocalContext_addJP(x_33, x_22, x_23, x_24);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_34);
x_1 = x_25;
x_2 = x_35;
goto _start;
}
}
case 10:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_IR_UnreachableBranches_findVarValue(x_37, x_2, x_3);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(x_40, x_38, x_42, x_2, x_41);
lean_dec(x_38);
lean_dec(x_40);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_IR_UnreachableBranches_findArgValue(x_44, x_2, x_3);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_IR_UnreachableBranches_updateCurrFnSummary(x_46, x_2, x_47);
return x_48;
}
case 12:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_2, 3);
lean_inc(x_51);
x_52 = l_Lean_IR_LocalContext_getJPParams(x_51, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = l_Array_empty___closed__1;
x_54 = l_Option_get_x21___rarg___closed__3;
x_55 = lean_panic_fn(x_54);
x_56 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_55, x_50, x_2, x_3);
lean_dec(x_50);
lean_dec(x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = 1;
x_61 = lean_unbox(x_58);
lean_dec(x_58);
x_62 = l_Bool_DecidableEq(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_2);
x_63 = lean_box(0);
lean_ctor_set(x_56, 0, x_63);
return x_56;
}
else
{
lean_object* x_64; 
lean_free_object(x_56);
x_64 = l_Lean_IR_LocalContext_getJPBody(x_51, x_49);
lean_dec(x_49);
lean_dec(x_51);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_IR_Inhabited;
x_66 = lean_panic_fn(x_54);
x_1 = x_66;
x_3 = x_59;
goto _start;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_1 = x_68;
x_3 = x_59;
goto _start;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_56, 0);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_56);
x_72 = 1;
x_73 = lean_unbox(x_70);
lean_dec(x_70);
x_74 = l_Bool_DecidableEq(x_73, x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_IR_LocalContext_getJPBody(x_51, x_49);
lean_dec(x_49);
lean_dec(x_51);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Lean_IR_Inhabited;
x_79 = lean_panic_fn(x_54);
x_1 = x_79;
x_3 = x_71;
goto _start;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_1 = x_81;
x_3 = x_71;
goto _start;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_52, 0);
lean_inc(x_83);
lean_dec(x_52);
x_84 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_83, x_50, x_2, x_3);
lean_dec(x_50);
lean_dec(x_83);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = 1;
x_89 = lean_unbox(x_86);
lean_dec(x_86);
x_90 = l_Bool_DecidableEq(x_89, x_88);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_2);
x_91 = lean_box(0);
lean_ctor_set(x_84, 0, x_91);
return x_84;
}
else
{
lean_object* x_92; 
lean_free_object(x_84);
x_92 = l_Lean_IR_LocalContext_getJPBody(x_51, x_49);
lean_dec(x_49);
lean_dec(x_51);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = l_Lean_IR_Inhabited;
x_94 = l_Option_get_x21___rarg___closed__3;
x_95 = lean_panic_fn(x_94);
x_1 = x_95;
x_3 = x_87;
goto _start;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_1 = x_97;
x_3 = x_87;
goto _start;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_84, 0);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_84);
x_101 = 1;
x_102 = lean_unbox(x_99);
lean_dec(x_99);
x_103 = l_Bool_DecidableEq(x_102, x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_2);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
else
{
lean_object* x_106; 
x_106 = l_Lean_IR_LocalContext_getJPBody(x_51, x_49);
lean_dec(x_49);
lean_dec(x_51);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = l_Lean_IR_Inhabited;
x_108 = l_Option_get_x21___rarg___closed__3;
x_109 = lean_panic_fn(x_108);
x_1 = x_109;
x_3 = x_100;
goto _start;
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_1 = x_111;
x_3 = x_100;
goto _start;
}
}
}
}
}
default: 
{
lean_object* x_113; 
x_113 = lean_box(0);
x_4 = x_113;
goto block_12;
}
}
block_12:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = l_HashMap_Inhabited___closed__1;
x_14 = x_13;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(1);
x_14 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_12, x_13, x_3, x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_2 = x_11;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_Decl_Inhabited;
x_14 = lean_array_get(x_13, x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_18 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_17, x_12);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_12);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(x_15, x_7, x_22, x_6);
lean_dec(x_15);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_16, x_22, x_24);
if (x_4 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_27, x_12);
lean_dec(x_12);
x_29 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_18, x_28);
lean_dec(x_28);
lean_dec(x_18);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = 1;
x_3 = x_10;
x_4 = x_30;
x_6 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
x_32 = 0;
x_3 = x_10;
x_4 = x_32;
x_6 = x_26;
goto _start;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_12);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = 1;
x_3 = x_10;
x_4 = x_35;
x_6 = x_34;
goto _start;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_38 = lean_box(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
return x_39;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferStep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_5 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(x_4, x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_5);
x_8 = lean_array_get_size(x_3);
x_9 = 0;
lean_inc(x_8);
x_10 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(x_3, x_8, x_8, x_9, x_1, x_2);
lean_dec(x_1);
lean_dec(x_8);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_3);
x_14 = 0;
lean_inc(x_13);
x_15 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(x_3, x_13, x_13, x_14, x_1, x_12);
lean_dec(x_1);
lean_dec(x_13);
lean_dec(x_3);
return x_15;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_3 = l_Lean_IR_UnreachableBranches_inferStep(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = 1;
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Bool_DecidableEq(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_free_object(x_3);
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = 1;
x_15 = lean_unbox(x_12);
lean_dec(x_12);
x_16 = l_Bool_DecidableEq(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
x_2 = x_13;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_inferMain___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_inferMain___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_inferMain___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_inferMain___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_inferMain(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_16, x_14);
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_20 = lean_box(13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = x_21;
x_23 = lean_array_fset(x_11, x_2, x_22);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_15);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = x_26;
x_28 = lean_array_fset(x_11, x_2, x_27);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
x_31 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = x_32;
x_34 = lean_array_fset(x_11, x_2, x_33);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_34;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = l_Array_empty___closed__1;
x_8 = x_4;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_3);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = x_10;
x_12 = lean_array_fset(x_4, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
x_17 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_2, x_15);
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_20 = lean_box(13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = x_21;
x_23 = lean_array_fset(x_12, x_3, x_22);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
x_27 = x_26;
x_28 = lean_array_fset(x_12, x_3, x_27);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
x_31 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = x_32;
x_34 = lean_array_fset(x_12, x_3, x_33);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_34;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 3);
x_15 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_14);
lean_ctor_set(x_2, 3, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_20 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
return x_21;
}
}
case 1:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_23);
x_26 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_24);
lean_ctor_set(x_2, 3, x_26);
lean_ctor_set(x_2, 2, x_25);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_31 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_29);
x_32 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_30);
x_33 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
return x_33;
}
}
case 10:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 3);
x_37 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_1, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(x_1, x_38, x_36);
lean_ctor_set(x_2, 3, x_39);
return x_2;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(x_1, x_40, x_41, x_36);
lean_dec(x_40);
lean_ctor_set(x_2, 3, x_42);
return x_2;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_47 = l_HashMapImp_find___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_1, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(x_1, x_48, x_46);
x_50 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_45);
lean_ctor_set(x_50, 3, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(x_1, x_51, x_52, x_46);
lean_dec(x_51);
x_54 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_53);
return x_54;
}
}
}
default: 
{
lean_object* x_55; 
x_55 = lean_box(0);
x_3 = x_55;
goto block_12;
}
}
block_12:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_2);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_IR_FnBody_body(x_2);
x_8 = lean_box(13);
x_9 = l_Lean_IR_FnBody_setBody(x_2, x_8);
x_10 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_7);
x_11 = l_Lean_IR_FnBody_setBody(x_9, x_10);
return x_11;
}
else
{
return x_2;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDead(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_4);
lean_ctor_set(x_2, 3, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_10 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDead___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDead(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = l_Lean_IR_Decl_Inhabited;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = l_Lean_IR_Decl_name(x_12);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_2, x_10);
lean_dec(x_10);
x_15 = l_Lean_IR_UnreachableBranches_addFunctionSummary(x_5, x_13, x_14);
x_4 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = l_HashMap_Inhabited___closed__1;
x_13 = lean_array_get(x_12, x_1, x_2);
lean_inc(x_8);
x_14 = l_Lean_IR_UnreachableBranches_elimDead(x_13, x_8);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = x_14;
x_18 = lean_array_fset(x_11, x_2, x_17);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_IR_elimDeadBranches(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_7 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(x_6, x_1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = l_mkPersistentArray___rarg(x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_5);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lean_IR_UnreachableBranches_inferMain___main___rarg(x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
x_18 = l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1(x_1, x_16, x_8, x_8, x_5);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_18);
x_19 = l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2(x_17, x_6, x_1);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_24 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(x_23, x_1);
x_25 = lean_array_get_size(x_1);
x_26 = lean_box(0);
lean_inc(x_25);
x_27 = l_mkPersistentArray___rarg(x_25, x_26);
x_28 = lean_box(0);
lean_inc(x_21);
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_27);
x_31 = l_Lean_IR_UnreachableBranches_inferMain___main___rarg(x_29, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_25);
x_35 = l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1(x_1, x_33, x_25, x_25, x_21);
lean_dec(x_25);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
x_37 = l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2(x_34, x_23, x_1);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_elimDeadBranches___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Data_Option(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_ElimDeadBranches(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_UnreachableBranches_Value_Inhabited = _init_l_Lean_IR_UnreachableBranches_Value_Inhabited();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_Inhabited);
l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___closed__1 = _init_l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___closed__1();
lean_mark_persistent(l_Array_isEqv___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___closed__1);
l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1);
l_Lean_IR_UnreachableBranches_Value_HasBeq = _init_l_Lean_IR_UnreachableBranches_Value_HasBeq();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasBeq);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4);
l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1 = _init_l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1();
lean_mark_persistent(l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__1);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__2 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__2);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__3 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__3);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__4 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__4);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__5 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__5();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__5);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__6 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__6();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__6);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__7 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__7();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__7);
l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1);
l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat = _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat);
l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1);
l_Lean_IR_UnreachableBranches_Value_HasToString = _init_l_Lean_IR_UnreachableBranches_Value_HasToString();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasToString);
l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14 = _init_l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14);
l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1 = _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1);
l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2 = _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2);
l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12 = _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12);
l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9);
res = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_UnreachableBranches_functionSummariesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt);
lean_dec_ref(res);
l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1 = _init_l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
