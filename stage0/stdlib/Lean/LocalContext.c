// Lean compiler output
// Module: Lean.LocalContext
// Imports: Init.Data.Nat.Control Lean.Data.PersistentArray Lean.Expr Lean.Hygiene
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_LocalContext_mkEmpty___closed__3;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_size___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_LocalContext_sanitizeNames___closed__1;
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__12;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedLocalContext___closed__6;
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_isSubPrefixOfAux___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_LocalDecl_value___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__17;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10;
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__9;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13(lean_object*);
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_isSubPrefixOfAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__3(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_instInhabitedLocalDecl___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LocalContext_mkBinding___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___at_Lean_LocalContext_replaceFVarId___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LocalDecl_value___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext;
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__7;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_size___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3;
static lean_object* l_Lean_instInhabitedLocalContext___closed__1;
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__20;
lean_object* l_Lean_PersistentArray_pop___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__15;
LEAN_EXPORT uint64_t l_Lean_hashLocalDeclKind____x40_Lean_LocalContext___hyg_233_(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__13;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
static lean_object* l_Lean_LocalContext_get_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4(lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__3;
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__8;
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LocalContext_mkEmpty___closed__4;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object*);
static lean_object* l_Lean_instInhabitedLocalContext___closed__4;
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2;
static lean_object* l_Lean_LocalContext_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_instInhabitedLocalContext___closed__5;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at_Lean_LocalContext_replaceFVarId___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LocalContext_getFVarIds___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_LocalContext_get_x21___closed__3;
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object*, uint8_t);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_size___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LocalDecl_value___closed__1;
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object*);
lean_object* l_Lean_PersistentArray_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LocalContext_mkBinding___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6;
static lean_object* l_Lean_instReprLocalDeclKind___closed__1;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_LocalContext_erase___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3(size_t, size_t, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_size___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedLocalDecl___closed__4;
extern lean_object* l_Lean_pp_sanitizeNames;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_LocalContext_erase___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedLocalContext___closed__7;
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object*);
static lean_object* l_Lean_instInhabitedLocalContext___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3(lean_object*);
static lean_object* l_Lean_LocalContext_mkEmpty___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___at_Lean_LocalContext_replaceFVarId___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4(lean_object*);
static lean_object* l_Lean_instInhabitedLocalContext___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15(lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__19;
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_instInhabitedLocalDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4___boxed(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1(lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at_Lean_LocalContext_replaceFVarId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object*);
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__11;
LEAN_EXPORT lean_object* l_Lean_hashLocalDeclKind____x40_Lean_LocalContext___hyg_233____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___lambda__1___boxed(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__14;
static lean_object* l_Lean_LocalDecl_value___closed__3;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11(lean_object*);
static lean_object* l_Lean_instInhabitedLocalDecl___closed__1;
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__1;
static lean_object* l_Lean_instHashableLocalDeclKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_LocalDeclKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDeclKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LocalDeclKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalDeclKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDeclKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDeclKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_LocalDeclKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalDeclKind.default", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3;
x_2 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6;
x_2 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalDeclKind.implDetail", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3;
x_2 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6;
x_2 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalDeclKind.auxDecl", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3;
x_2 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6;
x_2 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprLocalDeclKind___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDeclKind_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_LocalDeclKind_toCtorIdx(x_1);
x_4 = l_Lean_LocalDeclKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_instDecidableEqLocalDeclKind(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_Lean_hashLocalDeclKind____x40_Lean_LocalContext___hyg_233_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint64_t x_4; 
x_4 = 2;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hashLocalDeclKind____x40_Lean_LocalContext___hyg_233____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_hashLocalDeclKind____x40_Lean_LocalContext___hyg_233_(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instHashableLocalDeclKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashLocalDeclKind____x40_Lean_LocalContext___hyg_233____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableLocalDeclKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableLocalDeclKind___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedLocalDecl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedLocalDecl___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_instInhabitedLocalDecl___closed__3;
x_4 = 0;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLocalDecl___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = lean_mk_local_decl(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 0;
x_7 = 0;
x_8 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*5 + 1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_local_decl_binder_info(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_isLet(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_index(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_fvarId(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_userName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_type(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_2);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_binderInfo(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_kind(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_LocalDecl_kind(x_1);
x_3 = 2;
x_4 = l_Lean_instDecidableEqLocalDeclKind(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_isAuxDecl(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_LocalDecl_kind(x_1);
x_3 = 0;
x_4 = l_Lean_instDecidableEqLocalDeclKind(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_isImplementationDetail(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* x_1) {
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
x_1 = lean_mk_string_unchecked("Lean.LocalContext", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalDecl.value", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let declaration expected", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalDecl_value___closed__2;
x_3 = lean_unsigned_to_nat(123u);
x_4 = lean_unsigned_to_nat(29u);
x_5 = l_Lean_LocalDecl_value___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_value___closed__4;
x_3 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_value(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_hasValue(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4 + 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedLocalDecl;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalDecl.setBinderInfo", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected let declaration", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalDecl_setBinderInfo___closed__1;
x_3 = lean_unsigned_to_nat(140u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_LocalDecl_setBinderInfo___closed__2;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* x_1, uint8_t x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_Lean_LocalDecl_setBinderInfo___closed__3;
x_11 = l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_LocalDecl_setBinderInfo(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_fvarId(x_1);
x_3 = l_Lean_Expr_fvar___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalDecl_toExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_LocalDecl_hasExprMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* x_1, uint8_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 1, x_2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_2);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*5 + 1, x_2);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_2);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_LocalDecl_setKind(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedLocalContext___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedLocalContext___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_instInhabitedLocalContext___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_instInhabitedLocalContext___closed__4;
x_2 = l_Lean_instInhabitedLocalContext___closed__3;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_instInhabitedLocalContext___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedLocalContext___closed__2;
x_3 = l_Lean_instInhabitedLocalContext___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLocalContext___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_LocalContext_mkEmpty___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_LocalContext_mkEmpty___closed__2;
x_3 = l_Lean_LocalContext_mkEmpty___closed__1;
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
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedLocalContext___closed__2;
x_3 = l_Lean_LocalContext_mkEmpty___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_LocalContext_mkEmpty___closed__4;
return x_2;
}
}
static lean_object* _init_l_Lean_LocalContext_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_mkEmpty___closed__4;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_PersistentHashMap_Node_isEmpty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_PersistentHashMap_Node_isEmpty___rarg(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_isEmpty___at_Lean_LocalContext_isEmpty___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_local_ctx_is_empty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
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
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_LocalContext_mkLocalDecl___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_4);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*4 + 1, x_6);
lean_inc(x_11);
x_12 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_8, x_2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lean_PersistentArray_push___rarg(x_9, x_13);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_4);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_5);
lean_ctor_set_uint8(x_19, sizeof(void*)*4 + 1, x_6);
lean_inc(x_19);
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_15, x_2, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = l_Lean_PersistentArray_push___rarg(x_16, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_17);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_LocalContext_mkLocalDecl___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_LocalContext_mkLocalDecl(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_LocalContext_mkLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = lean_local_ctx_mk_local_decl(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set(x_12, 4, x_5);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_7);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_9, x_2, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_PersistentArray_push___rarg(x_10, x_14);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set(x_20, 3, x_4);
lean_ctor_set(x_20, 4, x_5);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_7);
lean_inc(x_20);
x_21 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_16, x_2, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = l_Lean_PersistentArray_push___rarg(x_17, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_18);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lean_LocalContext_mkLetDecl(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_LocalContext_mkLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_local_ctx_mk_let_decl(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
x_11 = 0;
x_12 = 2;
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*4 + 1, x_12);
lean_inc(x_2);
x_14 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_9, x_2, x_5);
lean_inc(x_13);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_7, x_2, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = l_Lean_PersistentArray_push___rarg(x_8, x_16);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = 0;
x_23 = 2;
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_4);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*4 + 1, x_23);
lean_inc(x_2);
x_25 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_20, x_2, x_5);
lean_inc(x_24);
x_26 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_18, x_2, x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = l_Lean_PersistentArray_push___rarg(x_19, x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_25);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = l_Lean_LocalDecl_setIndex(x_2, x_6);
x_8 = l_Lean_LocalDecl_fvarId(x_7);
lean_inc(x_7);
x_9 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_8, x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = l_Lean_PersistentArray_push___rarg(x_5, x_10);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = l_Lean_LocalDecl_setIndex(x_2, x_15);
x_17 = l_Lean_LocalDecl_fvarId(x_16);
lean_inc(x_16);
x_18 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_12, x_17, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = l_Lean_PersistentArray_push___rarg(x_13, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_name_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_LocalContext_find_x3f___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_LocalContext_find_x3f___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = lean_local_ctx_find(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findFVar_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalContext.get!", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown free variable", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalContext_get_x21___closed__1;
x_3 = lean_unsigned_to_nat(243u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_LocalContext_get_x21___closed__2;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_LocalContext_get_x21___closed__3;
x_5 = l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = l_Lean_LocalContext_get_x21(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_getFVar_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_14 = lean_usize_shift_right(x_2, x_5);
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
x_20 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_LocalContext_contains___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_LocalContext_contains___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_LocalContext_contains___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_contains(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = l_Lean_LocalContext_contains(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_containsFVar(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(x_6, x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_array_push(x_4, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_usize_shift_right(x_2, x_3);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_LocalContext_getFVarIds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_LocalContext_getFVarIds___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_getFVarIds___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_getFVarIds___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_getFVarIds___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalContext_getFVarIds(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvar___override(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l_Lean_LocalContext_getFVarIds(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalContext_getFVars(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
lean_inc(x_1);
x_8 = l_Lean_PersistentArray_get_x21___rarg(x_5, x_1, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_pop___rarg(x_1);
x_1 = x_9;
goto _start;
}
else
{
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_LocalContext_erase___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_array_set(x_4, x_8, x_9);
x_23 = lean_usize_shift_right(x_2, x_5);
x_24 = l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(x_21, x_23, x_3);
lean_inc(x_24);
x_25 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_ctor_set(x_10, 0, x_24);
x_26 = lean_array_set(x_22, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_24);
lean_free_object(x_10);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_array_set(x_22, x_8, x_27);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_set(x_22, x_8, x_32);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_array_set(x_4, x_8, x_9);
x_36 = lean_usize_shift_right(x_2, x_5);
x_37 = l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(x_34, x_36, x_3);
lean_inc(x_37);
x_38 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_array_set(x_35, x_8, x_39);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_set(x_35, x_8, x_45);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_46);
return x_1;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_48 = x_10;
} else {
 lean_dec_ref(x_10);
 x_48 = lean_box(0);
}
x_49 = lean_array_set(x_4, x_8, x_9);
x_50 = lean_usize_shift_right(x_2, x_5);
x_51 = l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(x_47, x_50, x_3);
lean_inc(x_51);
x_52 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_array_set(x_49, x_8, x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
lean_dec(x_48);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_set(x_49, x_8, x_60);
lean_dec(x_8);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
default: 
{
lean_dec(x_8);
lean_dec(x_4);
return x_1;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_idxOfAux___at_Lean_LocalContext_erase___spec__3(x_63, x_3, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_64);
lean_dec(x_63);
return x_1;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_1, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_1, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec(x_66);
lean_inc(x_70);
x_71 = l_Array_eraseIdx___rarg(x_63, x_70, lean_box(0));
x_72 = l_Array_eraseIdx___rarg(x_64, x_70, lean_box(0));
lean_ctor_set(x_1, 1, x_72);
lean_ctor_set(x_1, 0, x_71);
return x_1;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
lean_dec(x_66);
lean_inc(x_73);
x_74 = l_Array_eraseIdx___rarg(x_63, x_73, lean_box(0));
x_75 = l_Array_eraseIdx___rarg(x_64, x_73, lean_box(0));
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickCmp(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_3);
x_6 = l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_3, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_1, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_3, x_2);
x_13 = l_Lean_LocalDecl_index(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_PersistentArray_set___rarg(x_4, x_13, x_14);
lean_dec(x_13);
x_16 = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(x_15);
x_17 = l_Lean_LocalDecl_isAuxDecl(x_11);
lean_dec(x_11);
if (x_17 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(x_2, x_5);
lean_dec(x_2);
lean_ctor_set(x_1, 2, x_18);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_3, x_2);
x_21 = l_Lean_LocalDecl_index(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_PersistentArray_set___rarg(x_4, x_21, x_22);
lean_dec(x_21);
x_24 = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(x_23);
x_25 = l_Lean_LocalDecl_isAuxDecl(x_19);
lean_dec(x_19);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_5);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(x_2, x_5);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_LocalContext_erase___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at_Lean_LocalContext_erase___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_eraseAux___at_Lean_LocalContext_erase___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lean_LocalContext_erase___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
lean_inc(x_3);
x_11 = l_Lean_PersistentArray_get_x21___rarg(x_8, x_3, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_LocalDecl_fvarId(x_16);
x_18 = l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_2, x_17);
x_19 = l_Lean_PersistentArray_pop___rarg(x_3);
x_20 = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(x_19);
x_21 = l_Lean_LocalDecl_isAuxDecl(x_16);
lean_dec(x_16);
if (x_21 == 0)
{
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(x_17, x_4);
lean_dec(x_17);
lean_ctor_set(x_1, 2, x_22);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = l_Lean_LocalDecl_fvarId(x_23);
x_25 = l_Lean_PersistentHashMap_erase___at_Lean_LocalContext_erase___spec__1(x_2, x_24);
x_26 = l_Lean_PersistentArray_pop___rarg(x_3);
x_27 = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(x_26);
x_28 = l_Lean_LocalDecl_isAuxDecl(x_23);
lean_dec(x_23);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_erase___at_Lean_LocalContext_erase___spec__4(x_24, x_4);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_LocalDecl_userName(x_12);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_9);
lean_dec(x_12);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_LocalDecl_userName(x_16);
x_18 = lean_name_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_16);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
x_10 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_LocalDecl_userName(x_12);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_9);
lean_dec(x_12);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_LocalDecl_userName(x_16);
x_18 = lean_name_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_16);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(x_1, x_3, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_1, x_6, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findFromUserName_x3f___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findFromUserName_x3f___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findFromUserName_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findFromUserName_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findFromUserName_x3f(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_usesUserName(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_name_append_index_after(x_2, x_3);
x_5 = l_Lean_LocalContext_usesUserName(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_erase_macro_scopes(x_2);
x_4 = l_Lean_LocalContext_usesUserName(x_1, x_3);
if (x_4 == 0)
{
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_getUnusedName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
x_7 = lean_nat_dec_lt(x_6, x_4);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = l_outOfBounds___rarg(x_2);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_get_x21___rarg(x_2, x_3, x_6);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_4 = l_Lean_LocalContext_get_x21(x_1, x_2);
x_5 = l_Lean_LocalDecl_setUserName(x_4, x_3);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_LocalDecl_fvarId(x_5);
lean_inc(x_5);
x_10 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_7, x_9, x_5);
x_11 = l_Lean_LocalDecl_index(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_13 = l_Lean_PersistentArray_set___rarg(x_8, x_11, x_12);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = l_Lean_LocalDecl_fvarId(x_5);
lean_inc(x_5);
x_18 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_14, x_17, x_5);
x_19 = l_Lean_LocalDecl_index(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = l_Lean_PersistentArray_set___rarg(x_15, x_19, x_20);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_16);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Lean_LocalContext_findFromUserName_x3f(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = l_Lean_LocalDecl_setUserName(x_13, x_3);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_inc(x_14);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_15, x_14);
x_17 = l_Lean_LocalDecl_index(x_14);
lean_ctor_set(x_7, 0, x_14);
x_18 = l_Lean_PersistentArray_set___rarg(x_5, x_17, x_7);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_LocalDecl_setUserName(x_19, x_3);
x_21 = l_Lean_LocalDecl_fvarId(x_20);
lean_inc(x_20);
x_22 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_21, x_20);
x_23 = l_Lean_LocalDecl_index(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = l_Lean_PersistentArray_set___rarg(x_5, x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_27 = x_7;
} else {
 lean_dec_ref(x_7);
 x_27 = lean_box(0);
}
x_28 = l_Lean_LocalDecl_setUserName(x_26, x_3);
x_29 = l_Lean_LocalDecl_fvarId(x_28);
lean_inc(x_28);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_29, x_28);
x_31 = l_Lean_LocalDecl_index(x_28);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_28);
x_33 = l_Lean_PersistentArray_set___rarg(x_5, x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_6);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_renameUserName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_apply_1(x_3, x_13);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_inc(x_14);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_15, x_14);
x_17 = l_Lean_LocalDecl_index(x_14);
lean_ctor_set(x_7, 0, x_14);
x_18 = l_Lean_PersistentArray_set___rarg(x_5, x_17, x_7);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_apply_1(x_3, x_19);
x_21 = l_Lean_LocalDecl_fvarId(x_20);
lean_inc(x_20);
x_22 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_21, x_20);
x_23 = l_Lean_LocalDecl_index(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = l_Lean_PersistentArray_set___rarg(x_5, x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_27 = x_7;
} else {
 lean_dec_ref(x_7);
 x_27 = lean_box(0);
}
x_28 = lean_apply_1(x_3, x_26);
x_29 = l_Lean_LocalDecl_fvarId(x_28);
lean_inc(x_28);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_29, x_28);
x_31 = l_Lean_LocalDecl_index(x_28);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_28);
x_33 = l_Lean_PersistentArray_set___rarg(x_5, x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_6);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = l_Lean_LocalDecl_setKind(x_13, x_3);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_inc(x_14);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_15, x_14);
x_17 = l_Lean_LocalDecl_index(x_14);
lean_ctor_set(x_7, 0, x_14);
x_18 = l_Lean_PersistentArray_set___rarg(x_5, x_17, x_7);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_LocalDecl_setKind(x_19, x_3);
x_21 = l_Lean_LocalDecl_fvarId(x_20);
lean_inc(x_20);
x_22 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_21, x_20);
x_23 = l_Lean_LocalDecl_index(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = l_Lean_PersistentArray_set___rarg(x_5, x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_27 = x_7;
} else {
 lean_dec_ref(x_7);
 x_27 = lean_box(0);
}
x_28 = l_Lean_LocalDecl_setKind(x_26, x_3);
x_29 = l_Lean_LocalDecl_fvarId(x_28);
lean_inc(x_28);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_29, x_28);
x_31 = l_Lean_LocalDecl_index(x_28);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_28);
x_33 = l_Lean_PersistentArray_set___rarg(x_5, x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_6);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_LocalContext_setKind(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = l_Lean_LocalDecl_setBinderInfo(x_13, x_3);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_inc(x_14);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_15, x_14);
x_17 = l_Lean_LocalDecl_index(x_14);
lean_ctor_set(x_7, 0, x_14);
x_18 = l_Lean_PersistentArray_set___rarg(x_5, x_17, x_7);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_LocalDecl_setBinderInfo(x_19, x_3);
x_21 = l_Lean_LocalDecl_fvarId(x_20);
lean_inc(x_20);
x_22 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_21, x_20);
x_23 = l_Lean_LocalDecl_index(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = l_Lean_PersistentArray_set___rarg(x_5, x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_27 = x_7;
} else {
 lean_dec_ref(x_7);
 x_27 = lean_box(0);
}
x_28 = l_Lean_LocalDecl_setBinderInfo(x_26, x_3);
x_29 = l_Lean_LocalDecl_fvarId(x_28);
lean_inc(x_28);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_4, x_29, x_28);
x_31 = l_Lean_LocalDecl_index(x_28);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_28);
x_33 = l_Lean_PersistentArray_set___rarg(x_5, x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_6);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_LocalContext_setBinderInfo(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_outOfBounds___rarg(x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_get_x21___rarg(x_3, x_4, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_getAt_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___rarg___lambda__1), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = l_Lean_PersistentArray_foldlM___rarg(x_1, lean_box(0), x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_LocalContext_foldlM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_2(x_2, x_8, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___rarg___lambda__1), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lean_PersistentArray_foldrM___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Lean_PersistentArray_forM___rarg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_PersistentArray_findSomeM_x3f___rarg(x_1, lean_box(0), x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_PersistentArray_findSomeRevM_x3f___rarg(x_1, lean_box(0), x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclRevM_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_14);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_array_uget(x_8, x_10);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg(x_1, x_2, x_3, x_16, x_18);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__2), 5, 4);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_7);
lean_closure_set(x_20, 3, x_5);
lean_inc(x_5);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_box_usize(x_10);
x_23 = lean_box_usize(x_9);
x_24 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__3___boxed), 11, 10);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_6);
lean_closure_set(x_24, 7, x_7);
lean_closure_set(x_24, 8, x_8);
lean_closure_set(x_24, 9, x_23);
x_25 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___boxed), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__2), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_4);
x_19 = lean_box_usize(x_9);
x_20 = lean_box_usize(x_8);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_20);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_25, x_18);
x_27 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_apply_2(x_2, x_28, x_17);
x_30 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_29, x_18);
x_31 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_30, x_21);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_array_size(x_6);
x_12 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_6, x_11, x_12, x_10);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__2), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_7);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = lean_array_size(x_16);
x_22 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg(x_1, x_2, x_16, x_17, x_18, x_19, x_16, x_21, x_22, x_20);
lean_inc(x_17);
x_24 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__2), 3, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_17);
x_25 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_apply_2(x_9, lean_box(0), x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_15, lean_box(0), x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
lean_inc(x_22);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_20);
lean_closure_set(x_25, 2, x_22);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__1), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_3);
x_19 = lean_box_usize(x_9);
x_20 = lean_box_usize(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__2___boxed), 10, 9);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_20);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_25, x_18);
x_27 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_apply_2(x_2, x_28, x_17);
x_30 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_29, x_18);
x_31 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_30, x_21);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_array_size(x_12);
x_16 = 0;
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg(x_1, x_3, x_4, x_11, x_12, x_13, x_12, x_15, x_16, x_14);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__2), 3, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg(x_1, x_2, x_4, x_6, x_4);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__3), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg(x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDecl___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_usize_shift_right(x_3, x_4);
x_8 = lean_usize_to_nat(x_7);
x_9 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
lean_inc(x_1);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg(x_1, x_6, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_usize_to_nat(x_3);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg(x_1, x_26, x_31, x_32, x_5);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_le(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_usize_of_nat(x_4);
x_11 = lean_ctor_get_usize(x_2, 4);
lean_inc(x_1);
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(x_1, x_9, x_10, x_11, x_3);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_1);
return x_12;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg(x_1, x_13, x_17, x_18, x_12);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_nat_sub(x_4, x_7);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg(x_1, x_20, x_25, x_26, x_3);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_29 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg(x_1, x_28, x_3);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_5, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_1);
return x_29;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg(x_1, x_30, x_34, x_35, x_29);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(x_2, x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__7___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_foldl___spec__3___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__9___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__13___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_foldl___spec__11___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_foldl___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_foldl___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_foldlM___at_Lean_LocalContext_foldl___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LocalContext_foldl___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_5);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg(x_1, x_4, x_14, x_15, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_le(x_18, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_18);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = 0;
x_24 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg(x_1, x_17, x_22, x_23, x_3);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_18);
if (x_26 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 0;
x_29 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg(x_1, x_17, x_27, x_28, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_5);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg(x_1, x_4, x_14, x_15, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_le(x_18, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_18);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = 0;
x_24 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg(x_1, x_17, x_22, x_23, x_3);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_18);
if (x_26 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 0;
x_29 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg(x_1, x_17, x_27, x_28, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_5);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg(x_1, x_4, x_14, x_15, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_le(x_18, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_18);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = 0;
x_24 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg(x_1, x_17, x_22, x_23, x_3);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_18);
if (x_26 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 0;
x_29 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg(x_1, x_17, x_27, x_28, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg(x_1, x_9, x_5);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_5);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_5);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg(x_1, x_4, x_14, x_15, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_le(x_18, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_18);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = 0;
x_24 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg(x_1, x_17, x_22, x_23, x_3);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_18);
if (x_26 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 0;
x_29 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg(x_1, x_17, x_27, x_28, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 0);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg(x_1, x_9, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg(x_1, x_4, x_11, x_12, x_3);
x_14 = lean_ctor_get(x_2, 0);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg(x_1, x_14, x_13);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg(x_1, x_18, x_3);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_21 = 0;
lean_inc(x_1);
x_22 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg(x_1, x_4, x_20, x_21, x_3);
x_23 = lean_ctor_get(x_2, 0);
x_24 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg(x_1, x_23, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__4___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__6___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__7___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__8___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__10___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__11___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__12___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__13___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__9___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__15___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__16___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__17___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__18___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__14___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__19___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__21___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__22___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__23___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_LocalContext_foldr___spec__24___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at_Lean_LocalContext_foldr___spec__20___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldrM___at_Lean_LocalContext_foldr___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldrM___at_Lean_LocalContext_foldr___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldr___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4(x_6, x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_usize_shift_right(x_2, x_3);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_size___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_size___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_size___spec__2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_LocalContext_foldlM___at_Lean_LocalContext_size___spec__1(x_1, x_2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_LocalContext_size___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_LocalContext_size___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_size___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_size___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at_Lean_LocalContext_size___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_LocalContext_size___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldlM___at_Lean_LocalContext_size___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalContext_size(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_5, x_7);
lean_inc(x_1);
x_11 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(x_1, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_7, x_12);
{
size_t _tmp_6 = x_13;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; 
x_10 = lean_array_uget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_7, x_11);
{
size_t _tmp_6 = x_12;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
size_t x_17; size_t x_18; 
lean_free_object(x_10);
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
{
size_t _tmp_6 = x_18;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_ctor_set(x_10, 0, x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
lean_inc(x_1);
x_28 = lean_apply_1(x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_7, x_29);
{
size_t _tmp_6 = x_30;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1() {
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
static lean_object* _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__2;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_box(0);
x_5 = lean_array_size(x_3);
x_6 = 0;
x_7 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1;
x_8 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(x_1, x_3, x_4, x_7, x_3, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3;
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1;
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(x_1, x_12, x_13, x_16, x_12, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3;
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; 
x_10 = lean_array_uget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_7, x_11);
{
size_t _tmp_6 = x_12;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
size_t x_17; size_t x_18; 
lean_free_object(x_10);
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
{
size_t _tmp_6 = x_18;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_ctor_set(x_10, 0, x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
lean_inc(x_1);
x_28 = lean_apply_1(x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
size_t x_29; size_t x_30; 
x_29 = 1;
x_30 = lean_usize_add(x_7, x_29);
{
size_t _tmp_6 = x_30;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = lean_array_size(x_5);
x_8 = 0;
x_9 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1;
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(x_1, x_5, x_6, x_9, x_5, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3;
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_findDecl_x3f___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_LocalContext_findDecl_x3f___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDecl_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_12;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_12;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(x_1, x_3, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(x_1, x_6, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_array_get_size(x_3);
lean_inc(x_1);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclRev_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_LocalContext_findDeclRev_x3f___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_LocalContext_findDeclRev_x3f___spec__4___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_LocalContext_findDeclRev_x3f___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalContext_findDeclRev_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_isSubPrefixOfAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = l_Lean_LocalDecl_fvarId(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
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
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_get_x21___rarg(x_9, x_1, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_35 = lean_array_get_size(x_3);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
x_38 = lean_box(0);
x_15 = x_38;
goto block_34;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_41 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_isSubPrefixOfAux___spec__1(x_14, x_3, x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_15 = x_42;
goto block_34;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_14);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_4, x_43);
lean_dec(x_4);
x_4 = x_44;
goto _start;
}
}
block_34:
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_5, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_2);
x_19 = l_Lean_PersistentArray_get_x21___rarg(x_9, x_2, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_25 = l_Lean_LocalDecl_fvarId(x_23);
lean_dec(x_23);
x_26 = lean_name_eq(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_5 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_32 = lean_nat_add(x_5, x_30);
lean_dec(x_5);
x_4 = x_31;
x_5 = x_32;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_isSubPrefixOfAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_isSubPrefixOfAux___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_LocalContext_isSubPrefixOfAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_LocalContext_isSubPrefixOf(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.LocalContext.mkBinding", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_LocalDecl_value___closed__1;
x_2 = l_Lean_LocalContext_mkBinding___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(452u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_LocalContext_get_x21___closed__2;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_1, x_4);
x_8 = l_Lean_LocalContext_findFVar_x3f(x_2, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = l_Lean_LocalContext_mkBinding___lambda__1___closed__2;
x_10 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
lean_dec(x_11);
x_15 = lean_expr_abstract_range(x_13, x_4, x_1);
lean_dec(x_13);
if (x_3 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Expr_forallE___override(x_12, x_15, x_6, x_14);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Expr_lam___override(x_12, x_15, x_6, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_11, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 4);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_expr_has_loose_bvar(x_6, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_expr_lower_loose_bvars(x_6, x_24, x_24);
lean_dec(x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_expr_abstract_range(x_19, x_4, x_1);
lean_dec(x_19);
x_27 = lean_expr_abstract_range(x_20, x_4, x_1);
lean_dec(x_20);
x_28 = l_Lean_Expr_letE___override(x_18, x_26, x_27, x_6, x_21);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_expr_abstract(x_4, x_3);
x_6 = lean_array_get_size(x_3);
x_7 = lean_box(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lambda__1___boxed), 6, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
x_9 = l_Nat_foldRev___rarg(x_6, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_LocalContext_mkBinding___lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_LocalContext_mkBinding(x_5, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = l_Lean_LocalContext_findFVar_x3f(x_2, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = l_Lean_LocalContext_mkBinding___lambda__1___closed__2;
x_9 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_dec(x_10);
x_14 = lean_expr_abstract_range(x_12, x_3, x_1);
lean_dec(x_12);
x_15 = l_Lean_Expr_lam___override(x_11, x_14, x_5, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
lean_dec(x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_expr_has_loose_bvar(x_5, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_expr_lower_loose_bvars(x_5, x_22, x_22);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_expr_abstract_range(x_17, x_3, x_1);
lean_dec(x_17);
x_25 = lean_expr_abstract_range(x_18, x_3, x_1);
lean_dec(x_18);
x_26 = l_Lean_Expr_letE___override(x_16, x_24, x_25, x_5, x_19);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_expr_abstract(x_3, x_2);
x_5 = lean_array_get_size(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkLambda___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
x_7 = l_Nat_foldRev___rarg(x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_LocalContext_mkLambda___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_mkLambda(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = l_Lean_LocalContext_findFVar_x3f(x_2, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = l_Lean_LocalContext_mkBinding___lambda__1___closed__2;
x_9 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_dec(x_10);
x_14 = lean_expr_abstract_range(x_12, x_3, x_1);
lean_dec(x_12);
x_15 = l_Lean_Expr_forallE___override(x_11, x_14, x_5, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
lean_dec(x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_expr_has_loose_bvar(x_5, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_expr_lower_loose_bvars(x_5, x_22, x_22);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_expr_abstract_range(x_17, x_3, x_1);
lean_dec(x_17);
x_25 = lean_expr_abstract_range(x_18, x_3, x_1);
lean_dec(x_18);
x_26 = l_Lean_Expr_letE___override(x_16, x_24, x_25, x_5, x_19);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_expr_abstract(x_3, x_2);
x_5 = lean_array_get_size(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_LocalContext_mkForall___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
x_7 = l_Nat_foldRev___rarg(x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_LocalContext_mkForall___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_mkForall(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg(x_2, x_3, x_4, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(x_1, x_2, x_8);
x_10 = lean_box_usize(x_4);
x_11 = lean_box_usize(x_5);
x_12 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg(x_2, x_3, x_4, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_box_usize(x_4);
x_10 = lean_box_usize(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_10);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_apply_2(x_13, lean_box(0), x_15);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_apply_1(x_2, x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_apply_2(x_22, lean_box(0), x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg(x_1, x_2, x_4, x_13, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_apply_2(x_21, lean_box(0), x_23);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg(x_1, x_2, x_16, x_25, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg(x_2, x_3, x_4, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_box_usize(x_4);
x_10 = lean_box_usize(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_10);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_apply_2(x_13, lean_box(0), x_15);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_apply_1(x_2, x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_apply_2(x_22, lean_box(0), x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg(x_2, x_3, x_5, x_14, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(x_4);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_anyM___spec__2___rarg(x_1, x_2, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__3___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__4___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_anyM___spec__5___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_anyM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_usize_add(x_1, x_8);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg(x_2, x_3, x_4, x_5, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_4, x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(x_1, x_2, x_3, x_9);
x_11 = lean_box_usize(x_5);
x_12 = lean_box_usize(x_6);
x_13 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_apply_2(x_16, lean_box(0), x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_usize_add(x_1, x_8);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg(x_2, x_3, x_4, x_5, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_4, x_5);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box_usize(x_5);
x_12 = lean_box_usize(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_12);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_18, x_10);
x_20 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_apply_1(x_2, x_21);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_10);
x_24 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_23, x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_apply_2(x_26, lean_box(0), x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg(x_1, x_2, x_3, x_5, x_14, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_apply_2(x_22, lean_box(0), x_24);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg(x_1, x_2, x_3, x_17, x_26, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_usize_add(x_1, x_8);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg(x_2, x_3, x_4, x_5, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_4, x_5);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box_usize(x_5);
x_12 = lean_box_usize(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_12);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_18, x_10);
x_20 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_apply_1(x_2, x_21);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_10);
x_24 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_23, x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_apply_2(x_26, lean_box(0), x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg(x_2, x_3, x_4, x_6, x_15, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(x_5);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_allM___spec__2___rarg(x_1, x_2, x_3, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg(x_1, x_3, x_5, x_4);
x_7 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___lambda__1(x_8, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__3___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___lambda__2(x_8, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__4___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___lambda__1(x_8, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_allM___spec__5___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_allM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(x_1, x_6);
lean_dec(x_6);
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
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
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
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__3(x_1, x_3, x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4(x_1, x_11, x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
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
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__5(x_1, x_5, x_10, x_11);
return x_12;
}
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_any___spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_any___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_any___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_any(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(x_1, x_6);
lean_dec(x_6);
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
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 1;
return x_13;
}
else
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__3(x_1, x_3, x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__4(x_1, x_11, x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 1;
return x_13;
}
else
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__5(x_1, x_5, x_10, x_11);
return x_12;
}
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at_Lean_LocalContext_all___spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_LocalContext_all___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at_Lean_LocalContext_all___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalContext_all(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
x_39 = lean_nat_dec_lt(x_11, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = l_outOfBounds___rarg(x_36);
if (lean_obj_tag(x_40) == 0)
{
x_3 = x_11;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_12 = x_42;
goto block_35;
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_PersistentArray_get_x21___rarg(x_36, x_37, x_11);
if (lean_obj_tag(x_43) == 0)
{
x_3 = x_11;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_12 = x_45;
goto block_35;
}
}
block_35:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_LocalDecl_userName(x_12);
x_14 = l_Lean_Name_hasMacroScopes(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_NameSet_contains(x_6, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_13, x_16);
x_3 = x_11;
x_4 = lean_box(0);
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_box(0);
lean_inc(x_13);
x_20 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_13, x_19);
x_21 = l_Lean_sanitizeName(x_13, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_25 = l_Lean_LocalContext_setUserName(x_5, x_24, x_22);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_25;
x_6 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_box(0);
lean_inc(x_13);
x_28 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_13, x_27);
x_29 = l_Lean_sanitizeName(x_13, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_33 = l_Lean_LocalContext_setUserName(x_5, x_32, x_30);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_33;
x_6 = x_28;
x_7 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_6);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_7);
return x_47;
}
}
}
static lean_object* _init_l_Lean_LocalContext_sanitizeNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_sanitizeNames;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_LocalContext_sanitizeNames___closed__1;
x_5 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_NameSet_empty;
lean_inc(x_8);
lean_inc(x_1);
x_10 = l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(x_1, x_8, x_8, lean_box(0), x_1, x_9, x_2);
lean_dec(x_8);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
lean_ctor_set(x_11, 1, x_12);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldRevM_loop___at_Lean_LocalContext_sanitizeNames___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = lean_local_ctx_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_LocalDecl_userName(x_5);
x_7 = l_Lean_LocalContext_findFromUserName_x3f(x_1, x_6);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_LocalDecl_fvarId(x_5);
lean_dec(x_5);
x_12 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
lean_dec(x_6);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_LocalDecl_fvarId(x_5);
lean_dec(x_5);
x_17 = l_Lean_LocalDecl_fvarId(x_15);
lean_dec(x_15);
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_PersistentHashMap_find_x3f___at_Lean_LocalContext_find_x3f___spec__1(x_9, x_6);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_LocalDecl_index(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
x_19 = lean_array_uset(x_8, x_3, x_18);
x_3 = x_12;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_3, x_4);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___closed__1;
lean_inc(x_3);
x_10 = l_Array_qpartition___rarg(x_1, x_2, x_9, x_3, x_4, lean_box(0), lean_box(0), lean_box(0));
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_nat_dec_le(x_4, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2(x_1, x_12, x_3, x_11, lean_box(0), lean_box(0), lean_box(0));
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_11, x_15);
lean_dec(x_11);
x_2 = x_14;
x_3 = x_16;
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__1(x_1, x_3, x_4, x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; lean_object* x_14; 
lean_inc(x_8);
x_12 = l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2(x_6, x_5, x_8, x_8, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_8);
lean_dec(x_6);
x_13 = lean_array_size(x_12);
x_14 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3(x_13, x_4, x_12);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; lean_object* x_17; 
x_15 = l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2(x_6, x_5, x_9, x_8, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_8);
lean_dec(x_6);
x_16 = lean_array_size(x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3(x_16, x_4, x_15);
return x_17;
}
}
else
{
size_t x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_6);
x_18 = lean_array_size(x_5);
x_19 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3(x_18, x_4, x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_sortFVarsByContextOrder___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadLCtxOfMonadLift___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_14);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_array_uget(x_8, x_10);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg(x_1, x_2, x_3, x_16, x_18);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__1), 5, 4);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_7);
lean_closure_set(x_20, 3, x_5);
lean_inc(x_5);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_box_usize(x_10);
x_23 = lean_box_usize(x_9);
x_24 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__2___boxed), 11, 10);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_6);
lean_closure_set(x_24, 7, x_7);
lean_closure_set(x_24, 8, x_8);
lean_closure_set(x_24, 9, x_23);
x_25 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__1), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_4);
x_19 = lean_box_usize(x_9);
x_20 = lean_box_usize(x_8);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_20);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_25, x_18);
x_27 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = l_Lean_LocalDecl_isImplementationDetail(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l_Lean_LocalDecl_toExpr(x_28);
lean_dec(x_28);
x_31 = lean_array_push(x_17, x_30);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
lean_inc(x_33);
x_35 = lean_apply_2(x_33, lean_box(0), x_34);
x_36 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_36, 0, x_31);
lean_closure_set(x_36, 1, x_33);
x_37 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_35, x_36);
x_38 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_37, x_18);
x_39 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_38, x_21);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_28);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
lean_inc(x_41);
x_43 = lean_apply_2(x_41, lean_box(0), x_42);
x_44 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_44, 0, x_17);
lean_closure_set(x_44, 1, x_41);
x_45 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_43, x_44);
x_46 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_45, x_18);
x_47 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_46, x_21);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_LocalContext_instForInLocalDecl___spec__2___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_array_size(x_6);
x_12 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_6, x_11, x_12, x_10);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg___lambda__1), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_7);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = lean_array_size(x_16);
x_22 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg(x_1, x_2, x_16, x_17, x_18, x_19, x_16, x_21, x_22, x_20);
lean_inc(x_17);
x_24 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg___lambda__1), 3, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_17);
x_25 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_apply_2(x_9, lean_box(0), x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_15, lean_box(0), x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
lean_inc(x_22);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_LocalContext_instForInLocalDecl___spec__3___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_20);
lean_closure_set(x_25, 2, x_22);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__1), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_3);
x_19 = lean_box_usize(x_9);
x_20 = lean_box_usize(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__2___boxed), 10, 9);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_20);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_25, x_18);
x_27 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = l_Lean_LocalDecl_isImplementationDetail(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l_Lean_LocalDecl_toExpr(x_28);
lean_dec(x_28);
x_31 = lean_array_push(x_17, x_30);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
lean_inc(x_33);
x_35 = lean_apply_2(x_33, lean_box(0), x_34);
x_36 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_36, 0, x_31);
lean_closure_set(x_36, 1, x_33);
x_37 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_35, x_36);
x_38 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_37, x_18);
x_39 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_38, x_21);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_28);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
lean_inc(x_41);
x_43 = lean_apply_2(x_41, lean_box(0), x_42);
x_44 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_44, 0, x_17);
lean_closure_set(x_44, 1, x_41);
x_45 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_43, x_44);
x_46 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_45, x_18);
x_47 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_46, x_21);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_LocalContext_instForInLocalDecl___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_array_size(x_12);
x_16 = 0;
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg(x_1, x_3, x_4, x_11, x_12, x_13, x_12, x_15, x_16, x_14);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PersistentArray_forInAux___at_Lean_getLocalHyps___spec__2___rarg(x_1, x_2, x_4, x_6, x_4);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_PersistentArray_forIn___at_Lean_getLocalHyps___spec__1___rarg(x_1, x_2, x_5, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_getLocalHyps___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_Lean_LocalContext_getFVarIds___closed__1;
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_getLocalHyps___rarg___lambda__2), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getLocalHyps___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___lambda__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_getLocalHyps___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = l_Lean_Expr_replaceFVarId(x_12, x_1, x_2);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4 + 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
lean_inc(x_1);
x_20 = l_Lean_Expr_replaceFVarId(x_18, x_1, x_2);
lean_dec(x_18);
x_21 = l_Lean_Expr_replaceFVarId(x_19, x_1, x_2);
lean_dec(x_19);
lean_ctor_set(x_3, 4, x_21);
lean_ctor_set(x_3, 3, x_20);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 1);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_1);
x_29 = l_Lean_Expr_replaceFVarId(x_25, x_1, x_2);
lean_dec(x_25);
x_30 = l_Lean_Expr_replaceFVarId(x_26, x_1, x_2);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*5 + 1, x_28);
return x_31;
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_6, 1, x_13);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_1);
x_18 = lean_apply_1(x_1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_uset(x_8, x_3, x_19);
x_3 = x_10;
x_4 = x_20;
goto _start;
}
}
case 1:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_1);
x_24 = l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(x_1, x_23);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
lean_inc(x_1);
x_28 = l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(x_1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_10;
x_4 = x_30;
goto _start;
}
}
default: 
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(2);
x_33 = lean_array_uset(x_8, x_3, x_32);
x_3 = x_10;
x_4 = x_33;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___at_Lean_LocalContext_replaceFVarId___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_push(x_4, x_9);
x_3 = x_11;
x_4 = x_12;
x_5 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_mapM_x27_go___at_Lean_LocalContext_replaceFVarId___spec__6(x_1, x_2, x_5, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4(x_1, x_5, x_6, x_4);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_size(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4(x_1, x_9, x_10, x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5(x_1, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at_Lean_LocalContext_replaceFVarId___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at_Lean_LocalContext_replaceFVarId___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8(x_1, x_2, x_7);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_array_uset(x_9, x_4, x_12);
x_4 = x_11;
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_1);
x_17 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_16);
lean_ctor_set(x_7, 0, x_17);
x_18 = lean_array_uset(x_9, x_4, x_7);
x_4 = x_11;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
lean_inc(x_1);
x_21 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_array_uset(x_9, x_4, x_22);
x_4 = x_11;
x_5 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9(x_1, x_2, x_10, x_11, x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10(x_1, x_2, x_16, x_17, x_15);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_array_size(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10(x_1, x_2, x_20, x_21, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_array_uset(x_9, x_4, x_12);
x_4 = x_11;
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_1);
x_17 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_16);
lean_ctor_set(x_7, 0, x_17);
x_18 = lean_array_uset(x_9, x_4, x_7);
x_4 = x_11;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
lean_inc(x_1);
x_21 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_array_uset(x_9, x_4, x_22);
x_4 = x_11;
x_5 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_7 = l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8(x_1, x_2, x_5);
x_8 = lean_array_size(x_6);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11(x_1, x_2, x_8, x_9, x_6);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get_usize(x_3, 4);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8(x_1, x_2, x_11);
x_17 = lean_array_size(x_12);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11(x_1, x_2, x_17, x_18, x_12);
x_20 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set_usize(x_20, 4, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = lean_local_ctx_erase(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_LocalDecl_replaceFVarId___boxed), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(x_8, x_6);
x_10 = l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7(x_1, x_2, x_7);
lean_dec(x_2);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_LocalDecl_replaceFVarId___boxed), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
x_15 = l_Lean_PersistentHashMap_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__3(x_14, x_11);
x_16 = l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7(x_1, x_2, x_12);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__4(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___at_Lean_LocalContext_replaceFVarId___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapM_x27_go___at_Lean_LocalContext_replaceFVarId___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapM_x27___at_Lean_LocalContext_replaceFVarId___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__10(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_mapMAux___at_Lean_LocalContext_replaceFVarId___spec__8(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_replaceFVarId___spec__11(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_mapM___at_Lean_LocalContext_replaceFVarId___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_Nat_Control(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Hygiene(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Control(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_LocalDeclKind_noConfusion___rarg___closed__1 = _init_l_Lean_LocalDeclKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_LocalDeclKind_noConfusion___rarg___closed__1);
l_Lean_instInhabitedLocalDeclKind = _init_l_Lean_instInhabitedLocalDeclKind();
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__1 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__1();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__1);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__2);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__3);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__4 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__4();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__4);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__5 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__5();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__5);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__6);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__7 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__7();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__7);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__8 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__8();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__8);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__9 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__9();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__9);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__10);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__11 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__11();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__11);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__12 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__12();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__12);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__13 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__13();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__13);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__14 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__14();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__14);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__15 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__15();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__15);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__16);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__17 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__17();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__17);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__18 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__18();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__18);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__19 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__19();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__19);
l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__20 = _init_l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__20();
lean_mark_persistent(l_Lean_reprLocalDeclKind____x40_Lean_LocalContext___hyg_18____closed__20);
l_Lean_instReprLocalDeclKind___closed__1 = _init_l_Lean_instReprLocalDeclKind___closed__1();
lean_mark_persistent(l_Lean_instReprLocalDeclKind___closed__1);
l_Lean_instReprLocalDeclKind = _init_l_Lean_instReprLocalDeclKind();
lean_mark_persistent(l_Lean_instReprLocalDeclKind);
l_Lean_instHashableLocalDeclKind___closed__1 = _init_l_Lean_instHashableLocalDeclKind___closed__1();
lean_mark_persistent(l_Lean_instHashableLocalDeclKind___closed__1);
l_Lean_instHashableLocalDeclKind = _init_l_Lean_instHashableLocalDeclKind();
lean_mark_persistent(l_Lean_instHashableLocalDeclKind);
l_Lean_instInhabitedLocalDecl___closed__1 = _init_l_Lean_instInhabitedLocalDecl___closed__1();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl___closed__1);
l_Lean_instInhabitedLocalDecl___closed__2 = _init_l_Lean_instInhabitedLocalDecl___closed__2();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl___closed__2);
l_Lean_instInhabitedLocalDecl___closed__3 = _init_l_Lean_instInhabitedLocalDecl___closed__3();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl___closed__3);
l_Lean_instInhabitedLocalDecl___closed__4 = _init_l_Lean_instInhabitedLocalDecl___closed__4();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl___closed__4);
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
l_Lean_instInhabitedLocalContext___closed__1 = _init_l_Lean_instInhabitedLocalContext___closed__1();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__1);
l_Lean_instInhabitedLocalContext___closed__2 = _init_l_Lean_instInhabitedLocalContext___closed__2();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__2);
l_Lean_instInhabitedLocalContext___closed__3 = _init_l_Lean_instInhabitedLocalContext___closed__3();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__3);
l_Lean_instInhabitedLocalContext___closed__4 = _init_l_Lean_instInhabitedLocalContext___closed__4();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__4);
l_Lean_instInhabitedLocalContext___closed__5 = _init_l_Lean_instInhabitedLocalContext___closed__5();
l_Lean_instInhabitedLocalContext___closed__6 = _init_l_Lean_instInhabitedLocalContext___closed__6();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__6);
l_Lean_instInhabitedLocalContext___closed__7 = _init_l_Lean_instInhabitedLocalContext___closed__7();
lean_mark_persistent(l_Lean_instInhabitedLocalContext___closed__7);
l_Lean_instInhabitedLocalContext = _init_l_Lean_instInhabitedLocalContext();
lean_mark_persistent(l_Lean_instInhabitedLocalContext);
l_Lean_LocalContext_mkEmpty___closed__1 = _init_l_Lean_LocalContext_mkEmpty___closed__1();
lean_mark_persistent(l_Lean_LocalContext_mkEmpty___closed__1);
l_Lean_LocalContext_mkEmpty___closed__2 = _init_l_Lean_LocalContext_mkEmpty___closed__2();
lean_mark_persistent(l_Lean_LocalContext_mkEmpty___closed__2);
l_Lean_LocalContext_mkEmpty___closed__3 = _init_l_Lean_LocalContext_mkEmpty___closed__3();
lean_mark_persistent(l_Lean_LocalContext_mkEmpty___closed__3);
l_Lean_LocalContext_mkEmpty___closed__4 = _init_l_Lean_LocalContext_mkEmpty___closed__4();
lean_mark_persistent(l_Lean_LocalContext_mkEmpty___closed__4);
l_Lean_LocalContext_empty = _init_l_Lean_LocalContext_empty();
lean_mark_persistent(l_Lean_LocalContext_empty);
l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_LocalContext_mkLocalDecl___spec__2___closed__3);
l_Lean_LocalContext_get_x21___closed__1 = _init_l_Lean_LocalContext_get_x21___closed__1();
lean_mark_persistent(l_Lean_LocalContext_get_x21___closed__1);
l_Lean_LocalContext_get_x21___closed__2 = _init_l_Lean_LocalContext_get_x21___closed__2();
lean_mark_persistent(l_Lean_LocalContext_get_x21___closed__2);
l_Lean_LocalContext_get_x21___closed__3 = _init_l_Lean_LocalContext_get_x21___closed__3();
lean_mark_persistent(l_Lean_LocalContext_get_x21___closed__3);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_LocalContext_getFVarIds___spec__2___closed__1);
l_Lean_LocalContext_getFVarIds___closed__1 = _init_l_Lean_LocalContext_getFVarIds___closed__1();
lean_mark_persistent(l_Lean_LocalContext_getFVarIds___closed__1);
l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1 = _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__1);
l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__2 = _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__2);
l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3 = _init_l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3();
lean_mark_persistent(l_Lean_PersistentArray_findSomeMAux___at_Lean_LocalContext_findDecl_x3f___spec__3___rarg___closed__3);
l_Lean_LocalContext_mkBinding___lambda__1___closed__1 = _init_l_Lean_LocalContext_mkBinding___lambda__1___closed__1();
lean_mark_persistent(l_Lean_LocalContext_mkBinding___lambda__1___closed__1);
l_Lean_LocalContext_mkBinding___lambda__1___closed__2 = _init_l_Lean_LocalContext_mkBinding___lambda__1___closed__2();
lean_mark_persistent(l_Lean_LocalContext_mkBinding___lambda__1___closed__2);
l_Lean_LocalContext_sanitizeNames___closed__1 = _init_l_Lean_LocalContext_sanitizeNames___closed__1();
lean_mark_persistent(l_Lean_LocalContext_sanitizeNames___closed__1);
l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___closed__1 = _init_l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_LocalContext_sortFVarsByContextOrder___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
