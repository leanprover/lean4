// Lean compiler output
// Module: Lean.LocalContext
// Imports: Init Std.Data.PersistentArray Lean.Expr Lean.Hygiene
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
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_mkBinding_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_local_ctx_uses_user_name(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadLCtx(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType_match__1(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalDecl_userName___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1___boxed(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object*, lean_object*);
uint8_t lean_local_ctx_is_empty(lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4(lean_object*);
lean_object* l_Lean_LocalDecl_binderInfoEx_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2;
lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
lean_object* l_Lean_LocalDecl_setType_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_modifyLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value___closed__3;
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1(lean_object*, lean_object*, size_t, size_t, size_t, size_t, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object*);
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object*);
uint8_t l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4(lean_object*);
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_root___default___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceFVarIdAtLocalDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14(lean_object*);
lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index___boxed(lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__2(lean_object*, size_t, size_t);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_erase___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
extern lean_object* l_Option_instAlternativeOption___closed__1;
lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedLocalContext;
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2(lean_object*);
lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_addDecl___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Std_instInhabitedPersistentArray___closed__1;
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_LocalDecl_setUserName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__1;
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value___closed__2;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3(lean_object*);
lean_object* l_Lean_LocalContext_empty;
lean_object* lean_local_ctx_last_decl(lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_getFVars(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setIndex_match__1(lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_erase___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1;
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setUserName_match__1(lean_object*);
lean_object* l_Lean_LocalContext_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_insert___closed__1;
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg(lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_forM(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue_match__1(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10(lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo___lambda__1(uint8_t, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(lean_object*, lean_object*);
lean_object* lean_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_all___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl_match__1(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2;
lean_object* l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4(lean_object*);
uint8_t lean_local_decl_binder_info(lean_object*);
uint8_t l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setIndex_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRev_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* lean_mk_empty_local_ctx(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___at_Lean_LocalContext_mkLocalDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1(lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_findSomeM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21_match__1(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_rename_user_name(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3(lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23(lean_object*);
lean_object* l_Array_indexOfAux___at_Lean_LocalContext_erase___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value___closed__4;
lean_object* l_Lean_LocalContext_pop___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Lean_LocalDecl_value___closed__1;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12(lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_pop(lean_object*);
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4(lean_object*);
lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_isSubPrefixOfAux___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
lean_object* l_Lean_LocalContext_mkBinding_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__2;
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22(lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_LocalDecl_toExpr___boxed(lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_all(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo_match__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1(lean_object*);
lean_object* l_Array_anyMUnsafe_any___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux_match__1(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1(lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_LocalContext_pop___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_decls___default;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_allM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_renameUserName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4(lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDecl_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedLocalDecl___closed__1;
lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_LocalContext_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___at_Lean_LocalContext_erase___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDecl_x3f___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo___closed__3;
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldl(lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo___closed__1;
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19(lean_object*);
lean_object* l_Lean_LocalContext_get_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_pop___rarg(lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2(lean_object*);
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20(lean_object*);
lean_object* l_Lean_LocalDecl_binderInfoEx_match__1(lean_object*);
uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr___closed__1;
lean_object* l_Lean_LocalContext_get_x21___closed__2;
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_setBinderInfo___closed__2;
lean_object* l_Std_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13(lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_any___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setUserName(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedLocalContext___closed__1;
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21___closed__3;
lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalDecl_isLet_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2;
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_any(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21(lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instMonadLCtx___rarg(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5(lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9(lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3(lean_object*);
lean_object* l_Lean_LocalContext_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__6___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forIn_loop_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_fvarIdToDecl___default;
lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5(lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_isLet_match__1(lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_allM(lean_object*);
lean_object* l_Lean_LocalContext_anyM(lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_LocalContext_mkLetDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__6(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_contains___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOfAux___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8(lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6(lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
lean_object* l_Array_modify___at_Lean_LocalContext_mkLocalDecl___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setBinderInfo_match__1(lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_getAux___rarg___closed__1;
lean_object* l_Lean_LocalDecl_setIndex(lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedLocalDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_instInhabitedExpr___closed__1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLocalDecl___closed__1;
return x_1;
}
}
lean_object* lean_mk_local_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
}
lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = lean_mk_local_decl(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* lean_mk_let_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_6);
return x_7;
}
}
lean_object* l_Lean_LocalDecl_binderInfoEx_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
lean_object* l_Lean_LocalDecl_binderInfoEx_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_binderInfoEx_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t lean_local_decl_binder_info(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_local_decl_binder_info(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalDecl_isLet_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l_Lean_LocalDecl_isLet_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_isLet_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_LocalDecl_isLet(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_isLet(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalDecl_index(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_index___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_index(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setIndex_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_6(x_3, x_5, x_6, x_7, x_8, x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_18 = lean_box(x_17);
x_19 = lean_apply_7(x_4, x_12, x_13, x_14, x_15, x_16, x_18, x_2);
return x_19;
}
}
}
lean_object* l_Lean_LocalDecl_setIndex_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_setIndex_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setIndex(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_LocalDecl_fvarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_fvarId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_userName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_userName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_type(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_type(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_6(x_3, x_5, x_6, x_7, x_8, x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_18 = lean_box(x_17);
x_19 = lean_apply_7(x_4, x_12, x_13, x_14, x_15, x_16, x_18, x_2);
return x_19;
}
}
}
lean_object* l_Lean_LocalDecl_setType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_setType_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setType(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_2);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_16);
return x_17;
}
}
}
}
uint8_t l_Lean_LocalDecl_binderInfo(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_binderInfo(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = l_Lean_LocalDecl_binderInfo(x_1);
x_3 = l_Lean_BinderInfo_isAuxDecl(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_isAuxDecl(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalDecl_value_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_value_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.LocalContext");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.LocalDecl.value");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let declaration expected");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalDecl_value___closed__2;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(29u);
x_5 = l_Lean_LocalDecl_value___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_LocalDecl_value(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_Lean_LocalDecl_value___closed__4;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Lean_LocalDecl_value___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_value(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setValue_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_apply_7(x_3, x_6, x_7, x_8, x_9, x_10, x_12, x_2);
return x_13;
}
}
}
lean_object* l_Lean_LocalDecl_setValue_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_setValue_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setValue(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
lean_dec(x_4);
lean_ctor_set(x_1, 4, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_LocalDecl_setUserName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_6(x_3, x_5, x_6, x_7, x_8, x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_18 = lean_box(x_17);
x_19 = lean_apply_7(x_4, x_12, x_13, x_14, x_15, x_16, x_18, x_2);
return x_19;
}
}
}
lean_object* l_Lean_LocalDecl_setUserName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_setUserName_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setUserName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_dec(x_11);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_LocalDecl_setBinderInfo_match__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_box(x_2);
x_12 = lean_apply_6(x_3, x_5, x_6, x_7, x_8, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_19 = lean_box(x_18);
x_20 = lean_box(x_2);
x_21 = lean_apply_7(x_4, x_13, x_14, x_15, x_16, x_17, x_19, x_20);
return x_21;
}
}
}
lean_object* l_Lean_LocalDecl_setBinderInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_setBinderInfo_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_setBinderInfo_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_LocalDecl_setBinderInfo_match__1___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.LocalDecl.setBinderInfo");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected let declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalDecl_setBinderInfo___closed__1;
x_3 = lean_unsigned_to_nat(83u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_LocalDecl_setBinderInfo___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* x_1, uint8_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_2);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = l_Lean_instInhabitedLocalDecl;
x_10 = l_Lean_LocalDecl_setBinderInfo___closed__3;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_LocalDecl_setBinderInfo(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_LocalDecl_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_fvarId(x_1);
x_3 = l_Lean_mkFVar(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalDecl_toExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_toExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = l_Lean_Expr_hasExprMVar(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_ctor_get(x_1, 4);
x_6 = l_Lean_Expr_hasExprMVar(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasExprMVar(x_5);
return x_7;
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
lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_hasExprMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_LocalContext_fvarIdToDecl___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_root___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_LocalContext_fvarIdToDecl___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_decls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_2 = l_Std_instInhabitedPersistentArray___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLocalContext___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_2 = l_Std_PersistentArray_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_mk_empty_local_ctx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_LocalContext_mkEmpty___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_LocalContext_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_mkEmpty___closed__1;
return x_1;
}
}
uint8_t l_Std_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
uint8_t lean_local_ctx_is_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Std_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_local_ctx_is_empty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_mkLocalDecl_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_LocalContext_mkLocalDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkLocalDecl_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
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
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_6, x_16, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
}
lean_object* l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_box(2);
x_8 = lean_array_fset(x_1, x_2, x_7);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_array_fset(x_8, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Array_modify___at_Lean_LocalContext_mkLocalDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_name_eq(x_1, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_9, x_10, x_1, x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_name_eq(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_14, x_15, x_1, x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
}
case 1:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = x_3 >> x_4;
x_23 = x_5 + x_6;
x_24 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_21, x_22, x_23, x_1, x_2);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = x_3 >> x_4;
x_27 = x_5 + x_6;
x_28 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_25, x_26, x_27, x_1, x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
default: 
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 5;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_9 = x_2 & x_8;
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_box_usize(x_2);
x_12 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1;
x_13 = lean_box_usize(x_3);
x_14 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2;
x_15 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_11);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
x_16 = l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5(x_7, x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_19 = x_2 & x_18;
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_box_usize(x_2);
x_22 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1;
x_23 = lean_box_usize(x_3);
x_24 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2;
x_25 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1___boxed), 7, 6);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_21);
lean_closure_set(x_25, 3, x_22);
lean_closure_set(x_25, 4, x_23);
lean_closure_set(x_25, 5, x_24);
x_26 = l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5(x_17, x_20, x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__6(x_1, x_29, x_4, x_5);
x_31 = 7;
x_32 = x_31 <= x_3;
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_30);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_39 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(x_3, x_36, x_37, lean_box(0), x_29, x_38);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
else
{
return x_30;
}
}
else
{
return x_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__6(x_42, x_43, x_4, x_5);
x_45 = 7;
x_46 = x_45 <= x_3;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_44);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_53 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(x_3, x_50, x_51, lean_box(0), x_43, x_52);
lean_dec(x_51);
lean_dec(x_50);
return x_53;
}
else
{
return x_44;
}
}
else
{
return x_44;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_5, x_7, x_8, x_2, x_3);
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
x_16 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_12, x_14, x_15, x_2, x_3);
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
lean_object* l_Lean_LocalContext_mkLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_4);
lean_inc(x_8);
x_9 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_5, x_1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_Std_PersistentArray_push___rarg(x_6, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* lean_local_ctx_mk_local_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkLocalDecl___lambda__1___boxed), 6, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_6);
x_8 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_7);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Lean_LocalContext_mkLocalDecl___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_modify___at_Lean_LocalContext_mkLocalDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modify___at_Lean_LocalContext_mkLocalDecl___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___lambda__1(x_1, x_2, x_8, x_9, x_10, x_11, x_7);
return x_12;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_LocalContext_mkLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_LocalContext_mkLocalDecl___lambda__1(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = lean_local_ctx_mk_local_decl(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_LocalContext_mkLetDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_5);
lean_inc(x_9);
x_10 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_6, x_1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = l_Std_PersistentArray_push___rarg(x_7, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* lean_local_ctx_mk_let_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkLetDecl___lambda__1___boxed), 7, 5);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_7);
x_9 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_8);
return x_9;
}
}
lean_object* l_Lean_LocalContext_mkLetDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_LocalContext_mkLetDecl___lambda__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_local_ctx_mk_let_decl(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_LocalContext_addDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l_Lean_LocalDecl_setIndex(x_1, x_4);
x_6 = l_Lean_LocalDecl_fvarId(x_5);
lean_inc(x_5);
x_7 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_2, x_6, x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = l_Std_PersistentArray_push___rarg(x_3, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_LocalContext_addDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_addDecl___lambda__1), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* lean_local_ctx_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = lean_local_ctx_find(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findFVar_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_get_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_LocalContext_get_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_get_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.LocalContext.get!");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown free variable");
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalContext_get_x21___closed__1;
x_3 = lean_unsigned_to_nat(147u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_LocalContext_get_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_LocalContext_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_instInhabitedLocalDecl;
x_5 = l_Lean_LocalContext_get_x21___closed__3;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
return x_7;
}
}
}
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = l_Lean_LocalContext_get_x21(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_getFVar_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
uint8_t l_Std_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_LocalContext_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_contains(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_LocalContext_containsFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = l_Lean_LocalContext_contains(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_containsFVar(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__7(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_LocalDecl_fvarId(x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
}
static lean_object* _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__2___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4(x_5, x_2, x_3, x_6, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_array_get_size(x_8);
x_10 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(x_10, x_2, x_8, x_11, x_9);
lean_dec(x_9);
return x_12;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3;
x_7 = lean_usize_to_nat(x_6);
x_8 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3;
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1;
x_21 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4(x_20, x_16, x_5, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_usize_to_nat(x_2);
x_24 = lean_array_get_size(x_22);
x_25 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2;
x_26 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(x_25, x_4, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2;
x_15 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(x_14, x_11, x_12, x_4, x_13);
lean_dec(x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_nat_sub(x_3, x_6);
x_18 = lean_array_get_size(x_16);
x_19 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2;
x_20 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(x_19, x_2, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(x_21, x_2);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_array_get_size(x_23);
x_25 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2;
x_26 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(x_25, x_22, x_23, x_4, x_24);
lean_dec(x_24);
return x_26;
}
}
}
lean_object* l_Lean_LocalContext_getFVarIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Array_empty___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Std_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_getFVarIds___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalContext_getFVarIds(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_mkFVar(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_LocalContext_getFVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_LocalContext_getFVarIds(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = x_2;
x_7 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_4, x_5, x_6);
x_8 = x_7;
return x_8;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalContext_getFVars(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
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
x_7 = l_Std_PersistentArray_getAux___rarg___closed__1;
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
x_17 = lean_box(0);
x_18 = lean_usize_to_nat(x_2);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_nat_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_9 = l_Std_PersistentArray_getAux___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__2(x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_nat_sub(x_2, x_4);
lean_dec(x_4);
x_12 = lean_array_get(x_3, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_1, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_pop___rarg(x_1);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_7);
return x_1;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Std_PersistentArray_getAux___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_getAux___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_indexOfAux___at_Lean_LocalContext_erase___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_name_eq(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_indexOfAux___at_Lean_LocalContext_erase___spec__3(x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Array_eraseIdx_x27___rarg(x_2, x_12);
x_14 = l_Array_eraseIdx_x27___rarg(x_3, x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_3 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_2, x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_4, x_11);
lean_dec(x_11);
lean_dec(x_4);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_16 = lean_array_set(x_2, x_8, x_9);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
case 1:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_array_set(x_2, x_8, x_9);
x_24 = x_3 >> x_5;
x_25 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed), 6, 0);
x_26 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed), 4, 0);
x_27 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_22, x_24, x_4, x_25, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = lean_box(x_33);
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_dec(x_40);
x_41 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_ctor_set(x_10, 0, x_39);
x_42 = lean_array_set(x_23, x_8, x_10);
lean_dec(x_8);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = 1;
x_45 = lean_box(x_44);
lean_ctor_set(x_27, 1, x_45);
lean_ctor_set(x_27, 0, x_43);
return x_27;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_free_object(x_27);
lean_dec(x_39);
lean_free_object(x_10);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_set(x_23, x_8, x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = 1;
x_54 = lean_box(x_53);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_set(x_23, x_8, x_57);
lean_dec(x_8);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
lean_dec(x_27);
x_64 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_ctor_set(x_10, 0, x_63);
x_65 = lean_array_set(x_23, x_8, x_10);
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = 1;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_63);
lean_free_object(x_10);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_array_set(x_23, x_8, x_74);
lean_dec(x_8);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = 1;
x_78 = lean_box(x_77);
if (lean_is_scalar(x_73)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_73;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_10, 0);
lean_inc(x_80);
lean_dec(x_10);
x_81 = lean_array_set(x_2, x_8, x_9);
x_82 = x_3 >> x_5;
x_83 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed), 6, 0);
x_84 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed), 4, 0);
x_85 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_80, x_82, x_4, x_83, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
lean_dec(x_8);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = 0;
x_90 = lean_box(x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_93 = x_85;
} else {
 lean_dec_ref(x_85);
 x_93 = lean_box(0);
}
x_94 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_96 = lean_array_set(x_81, x_8, x_95);
lean_dec(x_8);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = 1;
x_99 = lean_box(x_98);
if (lean_is_scalar(x_93)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_93;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_93);
lean_dec(x_92);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
lean_dec(x_94);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_array_set(x_81, x_8, x_105);
lean_dec(x_8);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = 1;
x_109 = lean_box(x_108);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
default: 
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_111 = 0;
x_112 = lean_box(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__1;
x_5 = l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__2;
x_6 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Name_hash(x_2);
x_7 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed), 6, 0);
x_8 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed), 4, 0);
x_9 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_4, x_6, x_2, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Lean_Name_hash(x_2);
x_19 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed), 6, 0);
x_20 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed), 4, 0);
x_21 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_16, x_18, x_2, x_19, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_17, x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_LocalContext_erase___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Std_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_3, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_3, x_1);
x_8 = l_Lean_LocalDecl_index(x_6);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Std_PersistentArray_set___rarg(x_4, x_8, x_9);
lean_dec(x_8);
x_11 = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* lean_local_ctx_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_erase___lambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Array_indexOfAux___at_Lean_LocalContext_erase___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___at_Lean_LocalContext_erase___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___lambda__2(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_LocalContext_erase___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_erase___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_pop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_inc(x_3);
x_9 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_3, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Std_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_2, x_11);
x_13 = l_Std_PersistentArray_pop___rarg(x_3);
x_14 = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
lean_object* lean_local_ctx_pop(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_pop___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_pop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_pop___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_2, x_1, x_3, lean_box(0));
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_LocalDecl_userName(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_5);
lean_dec(x_8);
x_11 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_2, x_1, x_3, lean_box(0));
return x_11;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_LocalDecl_userName(x_12);
x_14 = lean_name_eq(x_13, x_2);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_2, x_1, x_3, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Option_instAlternativeOption___closed__1;
x_7 = l_Array_forIn_loop_match__1___rarg(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_fget(x_1, x_3);
lean_inc(x_2);
x_6 = l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(x_2, x_1, x_3, lean_box(0));
return x_7;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Option_instAlternativeOption___closed__1;
x_7 = l_Array_forIn_loop_match__1___rarg(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_2, x_1, x_3, lean_box(0));
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_LocalDecl_userName(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_5);
lean_dec(x_8);
x_11 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_2, x_1, x_3, lean_box(0));
return x_11;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_LocalDecl_userName(x_12);
x_14 = lean_name_eq(x_13, x_2);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_2, x_1, x_3, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Option_instAlternativeOption___closed__1;
x_7 = l_Array_forIn_loop_match__1___rarg(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(x_1, x_3, x_4, lean_box(0));
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_1, x_6, x_7, lean_box(0));
lean_dec(x_7);
return x_8;
}
}
}
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_inc(x_1);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_1, x_3, x_4, lean_box(0));
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
lean_object* lean_local_ctx_find_from_user_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(x_2, x_3);
return x_4;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t lean_local_ctx_uses_user_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_local_ctx_find_from_user_name(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_local_ctx_uses_user_name(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_appendIndexAfter(x_2, x_3);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_local_ctx_uses_user_name(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
}
}
lean_object* lean_local_ctx_get_unused_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_erase_macro_scopes(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_local_ctx_uses_user_name(x_1, x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(x_1, x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* lean_local_ctx_last_decl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_LocalContext_setUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_4 = l_Lean_LocalContext_get_x21(x_1, x_2);
x_5 = l_Lean_LocalDecl_setUserName(x_4, x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_LocalDecl_fvarId(x_5);
lean_inc(x_5);
x_8 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_6, x_7, x_5);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_LocalDecl_index(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = l_Std_PersistentArray_set___rarg(x_9, x_10, x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* l_Lean_LocalContext_renameUserName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = lean_local_ctx_find_from_user_name(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_LocalDecl_setUserName(x_8, x_3);
x_10 = l_Lean_LocalDecl_fvarId(x_9);
lean_inc(x_9);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_10, x_9);
x_12 = l_Lean_LocalDecl_index(x_9);
lean_ctor_set(x_6, 0, x_9);
x_13 = l_Std_PersistentArray_set___rarg(x_5, x_12, x_6);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_LocalDecl_setUserName(x_15, x_3);
x_17 = l_Lean_LocalDecl_fvarId(x_16);
lean_inc(x_16);
x_18 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_17, x_16);
x_19 = l_Lean_LocalDecl_index(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = l_Std_PersistentArray_set___rarg(x_5, x_19, x_20);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* lean_local_ctx_rename_user_name(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_LocalContext_renameUserName___lambda__1), 5, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_LocalContext_modifyLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_1(x_3, x_8);
x_10 = l_Lean_LocalDecl_fvarId(x_9);
lean_inc(x_9);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_10, x_9);
x_12 = l_Lean_LocalDecl_index(x_9);
lean_ctor_set(x_6, 0, x_9);
x_13 = l_Std_PersistentArray_set___rarg(x_5, x_12, x_6);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_1(x_3, x_15);
x_17 = l_Lean_LocalDecl_fvarId(x_16);
lean_inc(x_16);
x_18 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_17, x_16);
x_19 = l_Lean_LocalDecl_index(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = l_Std_PersistentArray_set___rarg(x_5, x_19, x_20);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_LocalContext_modifyLocalDecl___lambda__1), 5, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = l_Lean_LocalContext_mkLocalDecl_match__1___rarg(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_LocalContext_setBinderInfo___lambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalDecl_setBinderInfo(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_LocalContext_setBinderInfo___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_LocalContext_modifyLocalDecl(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_LocalContext_setBinderInfo___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_LocalContext_setBinderInfo___lambda__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_LocalContext_setBinderInfo(x_1, x_2, x_4);
return x_5;
}
}
lean_object* lean_local_ctx_num_indices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* lean_local_ctx_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_LocalContext_foldlM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_2(x_2, x_3, x_8);
return x_9;
}
}
}
lean_object* l_Lean_LocalContext_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___rarg___lambda__1), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
x_9 = l_Std_PersistentArray_foldlM___rarg(x_1, lean_box(0), x_7, x_8, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_LocalContext_foldlM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_foldlM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_LocalContext_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
}
lean_object* l_Lean_LocalContext_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Std_PersistentArray_forM___rarg(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_LocalContext_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Std_PersistentArray_findSomeM_x3f___rarg(x_1, lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Std_PersistentArray_findSomeRevM_x3f___rarg(x_1, lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclRevM_x3f___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg(x_5, x_3, x_4, x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__2), 3, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg(x_10, x_3, x_9, x_12, x_11);
lean_dec(x_11);
return x_13;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = x_3 >> x_4;
x_8 = lean_usize_to_nat(x_7);
x_9 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = x_11 << x_4;
x_13 = x_12 - x_11;
x_14 = x_3 & x_13;
x_15 = 5;
x_16 = x_4 - x_15;
lean_inc(x_1);
x_17 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_18, 0, x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_8, x_19);
lean_dec(x_8);
x_21 = lean_array_get_size(x_6);
x_22 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg(x_18, x_17, x_6, x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__2), 3, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_usize_to_nat(x_3);
x_26 = lean_array_get_size(x_23);
x_27 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg(x_24, x_5, x_23, x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
return x_27;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg(x_5, x_3, x_4, x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__2), 3, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg(x_10, x_3, x_9, x_12, x_11);
lean_dec(x_11);
return x_13;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__2), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_nat_dec_le(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_ctor_get_usize(x_2, 4);
x_13 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(x_1, x_10, x_11, x_12, x_3);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_array_get_size(x_14);
x_16 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg(x_5, x_13, x_14, x_6, x_15);
lean_dec(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_nat_sub(x_4, x_8);
x_19 = lean_array_get_size(x_17);
x_20 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg(x_5, x_3, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg(x_1, x_21, x_3);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg(x_5, x_22, x_23, x_6, x_24);
lean_dec(x_24);
return x_25;
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_LocalContext_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__11___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__13___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__16___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__15___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__19___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__18___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__21___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__20___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__17___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__23___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Lean_LocalContext_foldl___spec__22___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_foldl___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_1);
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
x_9 = l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(x_1, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
{
size_t _tmp_4 = x_11;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_1);
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; 
x_8 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
{
size_t _tmp_4 = x_10;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_5 + x_14;
{
size_t _tmp_4 = x_15;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_box(0);
x_5 = lean_array_get_size(x_3);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_findSomeM_x3f___rarg___closed__1;
x_9 = l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(x_1, x_8, x_3, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
return x_4;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_box(0);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_findSomeM_x3f___rarg___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(x_1, x_19, x_14, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
return x_15;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_1);
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; 
x_8 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
{
size_t _tmp_4 = x_10;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_5 + x_14;
{
size_t _tmp_4 = x_15;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_findSomeM_x3f___rarg___closed__1;
x_11 = l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(x_1, x_10, x_5, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_6;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_findDecl_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_LocalContext_findDecl_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDecl_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(x_2, x_1, x_3, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(x_2, x_1, x_3, lean_box(0));
return x_9;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Option_instAlternativeOption___closed__1;
x_7 = l_Array_forIn_loop_match__1___rarg(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_fget(x_1, x_3);
lean_inc(x_2);
x_6 = l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(x_2, x_1, x_3, lean_box(0));
return x_7;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Option_instAlternativeOption___closed__1;
x_7 = l_Array_forIn_loop_match__1___rarg(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(x_2, x_1, x_3, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(x_2, x_1, x_3, lean_box(0));
return x_9;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Option_instAlternativeOption___closed__1;
x_7 = l_Array_forIn_loop_match__1___rarg(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(x_1, x_3, x_4, lean_box(0));
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(x_1, x_6, x_7, lean_box(0));
lean_dec(x_7);
return x_8;
}
}
}
lean_object* l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_inc(x_1);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(x_1, x_3, x_4, lean_box(0));
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Std_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Std_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_findDeclRev_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclRev_x3f___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l_Lean_LocalContext_isSubPrefixOfAux___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = l_Lean_LocalDecl_fvarId(x_1);
x_5 = lean_name_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_1, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_LocalContext_isSubPrefixOfAux___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_14, x_3, x_16, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_5, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_2);
x_21 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_2, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_27 = l_Lean_LocalDecl_fvarId(x_25);
lean_dec(x_25);
x_28 = lean_name_eq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_4, x_32);
lean_dec(x_4);
x_34 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_4 = x_33;
x_5 = x_34;
goto _start;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_4, x_36);
lean_dec(x_4);
x_4 = x_37;
goto _start;
}
}
}
}
}
lean_object* l_Lean_LocalContext_isSubPrefixOfAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_isSubPrefixOfAux___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_LocalContext_isSubPrefixOfAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_LocalContext_isSubPrefixOfAux(x_4, x_5, x_3, x_6, x_6);
return x_7;
}
}
lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_LocalContext_isSubPrefixOf(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_LocalContext_mkBinding_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
lean_dec(x_7);
x_13 = lean_box(x_12);
x_14 = lean_apply_5(x_2, x_8, x_9, x_10, x_11, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_21 = lean_box(x_20);
x_22 = lean_apply_6(x_3, x_15, x_16, x_17, x_18, x_19, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_LocalContext_mkBinding_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.LocalContext.mkBinding");
return x_1;
}
}
static lean_object* _init_l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(331u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_LocalContext_get_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_array_get(x_10, x_3, x_9);
lean_inc(x_2);
x_12 = l_Lean_LocalContext_findFVar_x3f(x_2, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2;
x_14 = lean_panic_fn(x_10, x_13);
x_4 = x_9;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
lean_dec(x_16);
x_20 = lean_expr_abstract_range(x_18, x_9, x_3);
lean_dec(x_18);
if (x_1 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_mkForall(x_17, x_19, x_20, x_5);
x_4 = x_9;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_mkLambda(x_17, x_19, x_20, x_5);
x_4 = x_9;
x_5 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_16, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 4);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_16, sizeof(void*)*5);
lean_dec(x_16);
x_29 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_30 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_expr_abstract_range(x_26, x_9, x_3);
lean_dec(x_26);
x_33 = lean_expr_abstract_range(x_27, x_9, x_3);
lean_dec(x_27);
x_34 = l_Lean_mkLet(x_25, x_32, x_33, x_5, x_28);
x_4 = x_9;
x_5 = x_34;
goto _start;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Lean_LocalContext_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_expr_abstract(x_4, x_3);
x_6 = lean_array_get_size(x_3);
x_7 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_LocalContext_mkBinding(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_array_get(x_9, x_2, x_8);
lean_inc(x_1);
x_11 = l_Lean_LocalContext_findFVar_x3f(x_1, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2;
x_13 = lean_panic_fn(x_9, x_12);
x_3 = x_8;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
lean_dec(x_15);
x_19 = lean_expr_abstract_range(x_17, x_8, x_2);
lean_dec(x_17);
x_20 = l_Lean_mkLambda(x_16, x_18, x_19, x_4);
x_3 = x_8;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 4);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_15, sizeof(void*)*5);
lean_dec(x_15);
x_26 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_27 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_expr_abstract_range(x_23, x_8, x_2);
lean_dec(x_23);
x_30 = lean_expr_abstract_range(x_24, x_8, x_2);
lean_dec(x_24);
x_31 = l_Lean_mkLet(x_22, x_29, x_30, x_4, x_25);
x_3 = x_8;
x_4 = x_31;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_Lean_LocalContext_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_expr_abstract(x_3, x_2);
x_5 = lean_array_get_size(x_2);
x_6 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkLambda___spec__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkLambda___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_mkLambda(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_array_get(x_9, x_2, x_8);
lean_inc(x_1);
x_11 = l_Lean_LocalContext_findFVar_x3f(x_1, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2;
x_13 = lean_panic_fn(x_9, x_12);
x_3 = x_8;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
lean_dec(x_15);
x_19 = lean_expr_abstract_range(x_17, x_8, x_2);
lean_dec(x_17);
x_20 = l_Lean_mkForall(x_16, x_18, x_19, x_4);
x_3 = x_8;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 4);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_15, sizeof(void*)*5);
lean_dec(x_15);
x_26 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_27 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_expr_abstract_range(x_23, x_8, x_2);
lean_dec(x_23);
x_30 = lean_expr_abstract_range(x_24, x_8, x_2);
lean_dec(x_24);
x_31 = l_Lean_mkLet(x_22, x_29, x_30, x_4, x_25);
x_3 = x_8;
x_4 = x_31;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_Lean_LocalContext_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_expr_abstract(x_3, x_2);
x_5 = lean_array_get_size(x_2);
x_6 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkForall___spec__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_LocalContext_mkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev_loop___at_Lean_LocalContext_mkForall___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_mkForall(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
x_21 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
x_21 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg(x_1, x_5, x_4, x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg___lambda__1), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg(x_1, x_10, x_9, x_12, x_11);
lean_dec(x_11);
return x_13;
}
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
x_21 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg(x_2, x_3, x_5, x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(x_4);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(x_1, x_2, x_6);
x_8 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_LocalContext_anyM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___at_Lean_LocalContext_anyM___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
x_21 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
x_21 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_apply_1(x_3, x_12);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_5);
return x_14;
}
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg(x_1, x_6, x_5, x_8, x_7);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__2), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_2);
x_12 = lean_array_get_size(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg(x_1, x_11, x_10, x_13, x_12);
lean_dec(x_12);
return x_14;
}
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
x_21 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg(x_2, x_3, x_5, x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(x_4);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__2), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(x_1, x_2, x_3, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg(x_1, x_3, x_5, x_4);
x_7 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_LocalContext_allM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___at_Lean_LocalContext_allM___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8_t l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(x_1, x_2, x_10, x_11);
return x_12;
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8_t l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__6(x_1, x_2, x_10, x_11);
return x_12;
}
}
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = 0;
x_4 = lean_box(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
return x_6;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3(x_4, x_3, x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___lambda__1), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_array_get_size(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(x_9, x_8, x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(x_3, x_6, x_8, x_7);
lean_dec(x_7);
return x_9;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
uint8_t l_Lean_LocalContext_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(x_2, x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__6(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_any(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__3(x_4, x_3, x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_array_get_size(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(x_9, x_8, x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyMUnsafe___at_Lean_LocalContext_any___spec__5(x_3, x_6, x_8, x_7);
lean_dec(x_7);
return x_9;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
uint8_t l_Lean_LocalContext_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(x_2, x_3);
if (x_4 == 0)
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
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_LocalContext_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_all(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = l_Std_PersistentArray_get_x21___at___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux___spec__1(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_userName(x_12);
x_14 = l_Lean_NameSet_insert___closed__1;
x_15 = lean_box(0);
lean_inc(x_13);
lean_inc(x_3);
x_16 = l_Std_RBNode_insert___rarg(x_14, x_3, x_13, x_15);
x_17 = l_Lean_Name_hasMacroScopes(x_13);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_NameSet_contains(x_3, x_13);
lean_dec(x_3);
if (x_18 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
x_1 = x_8;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_sanitizeName(x_13, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_24 = l_Lean_LocalContext_setUserName(x_2, x_23, x_21);
x_1 = x_8;
x_2 = x_24;
x_3 = x_16;
x_4 = x_22;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_26 = l_Lean_sanitizeName(x_13, x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_30 = l_Lean_LocalContext_setUserName(x_2, x_29, x_27);
x_1 = x_8;
x_2 = x_30;
x_3 = x_16;
x_4 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
}
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_getSanitizeNames(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_NameSet_empty;
x_9 = l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(x_7, x_1, x_8, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
lean_ctor_set(x_10, 1, x_11);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
lean_object* l_Lean_instMonadLCtx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_Lean_instMonadLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadLCtx___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_LocalDecl_fvarId(x_3);
x_5 = lean_name_eq(x_4, x_1);
lean_dec(x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 3);
x_8 = l_Lean_Expr_replaceFVarId(x_7, x_1, x_2);
lean_dec(x_7);
lean_ctor_set(x_3, 3, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = l_Lean_Expr_replaceFVarId(x_12, x_1, x_2);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
lean_inc(x_1);
x_19 = l_Lean_Expr_replaceFVarId(x_17, x_1, x_2);
lean_dec(x_17);
x_20 = l_Lean_Expr_replaceFVarId(x_18, x_1, x_2);
lean_dec(x_18);
lean_ctor_set(x_3, 4, x_20);
lean_ctor_set(x_3, 3, x_19);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_1);
x_27 = l_Lean_Expr_replaceFVarId(x_24, x_1, x_2);
lean_dec(x_24);
x_28 = l_Lean_Expr_replaceFVarId(x_25, x_1, x_2);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_26);
return x_29;
}
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_replaceFVarIdAtLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_replaceFVarIdAtLocalDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_Data_PersistentArray(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Hygiene(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_LocalContext(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_PersistentArray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLocalDecl___closed__1 = _init_l_Lean_instInhabitedLocalDecl___closed__1();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl___closed__1);
l_Lean_instInhabitedLocalDecl = _init_l_Lean_instInhabitedLocalDecl();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl);
l_Lean_LocalDecl_value___closed__1 = _init_l_Lean_LocalDecl_value___closed__1();
lean_mark_persistent(l_Lean_LocalDecl_value___closed__1);
l_Lean_LocalDecl_value___closed__2 = _init_l_Lean_LocalDecl_value___closed__2();
lean_mark_persistent(l_Lean_LocalDecl_value___closed__2);
l_Lean_LocalDecl_value___closed__3 = _init_l_Lean_LocalDecl_value___closed__3();
lean_mark_persistent(l_Lean_LocalDecl_value___closed__3);
l_Lean_LocalDecl_value___closed__4 = _init_l_Lean_LocalDecl_value___closed__4();
lean_mark_persistent(l_Lean_LocalDecl_value___closed__4);
l_Lean_LocalDecl_setBinderInfo___closed__1 = _init_l_Lean_LocalDecl_setBinderInfo___closed__1();
lean_mark_persistent(l_Lean_LocalDecl_setBinderInfo___closed__1);
l_Lean_LocalDecl_setBinderInfo___closed__2 = _init_l_Lean_LocalDecl_setBinderInfo___closed__2();
lean_mark_persistent(l_Lean_LocalDecl_setBinderInfo___closed__2);
l_Lean_LocalDecl_setBinderInfo___closed__3 = _init_l_Lean_LocalDecl_setBinderInfo___closed__3();
lean_mark_persistent(l_Lean_LocalDecl_setBinderInfo___closed__3);
l_Lean_LocalContext_fvarIdToDecl___default___closed__1 = _init_l_Lean_LocalContext_fvarIdToDecl___default___closed__1();
lean_mark_persistent(l_Lean_LocalContext_fvarIdToDecl___default___closed__1);
l_Lean_LocalContext_fvarIdToDecl___default = _init_l_Lean_LocalContext_fvarIdToDecl___default();
lean_mark_persistent(l_Lean_LocalContext_fvarIdToDecl___default);
l_Lean_LocalContext_decls___default = _init_l_Lean_LocalContext_decls___default();
lean_mark_persistent(l_Lean_LocalContext_decls___default);
l_Lean_instInhabitedLocalContext___closed__1 = _init_l_Lean_instInhabitedLocalContext___closed__1();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__1);
l_Lean_instInhabitedLocalContext = _init_l_Lean_instInhabitedLocalContext();
lean_mark_persistent(l_Lean_instInhabitedLocalContext);
l_Lean_LocalContext_mkEmpty___closed__1 = _init_l_Lean_LocalContext_mkEmpty___closed__1();
lean_mark_persistent(l_Lean_LocalContext_mkEmpty___closed__1);
l_Lean_LocalContext_empty = _init_l_Lean_LocalContext_empty();
lean_mark_persistent(l_Lean_LocalContext_empty);
l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__1);
l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed__const__2);
l_Lean_LocalContext_get_x21___closed__1 = _init_l_Lean_LocalContext_get_x21___closed__1();
lean_mark_persistent(l_Lean_LocalContext_get_x21___closed__1);
l_Lean_LocalContext_get_x21___closed__2 = _init_l_Lean_LocalContext_get_x21___closed__2();
lean_mark_persistent(l_Lean_LocalContext_get_x21___closed__2);
l_Lean_LocalContext_get_x21___closed__3 = _init_l_Lean_LocalContext_get_x21___closed__3();
lean_mark_persistent(l_Lean_LocalContext_get_x21___closed__3);
l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1 = _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1();
lean_mark_persistent(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__1);
l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2 = _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2();
lean_mark_persistent(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___closed__2);
l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__1 = _init_l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__1);
l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__2 = _init_l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___closed__2);
l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__1 = _init_l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__1();
lean_mark_persistent(l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__1);
l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2 = _init_l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2();
lean_mark_persistent(l_Nat_foldRev_loop___at_Lean_LocalContext_mkBinding___spec__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
