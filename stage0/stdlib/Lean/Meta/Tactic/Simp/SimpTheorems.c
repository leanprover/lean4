// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpTheorems
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.DiscrTree Lean.Meta.AppBuilder Lean.Meta.Eqns Lean.Meta.Tactic.AuxLemma Lean.DocString Lean.PrettyPrinter
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_addSimpTheoremEntry___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isRflProofCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3;
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1;
static lean_object* l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2___closed__1;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpEntry;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__3;
static lean_object* l_Lean_Meta_isRflProofCore___closed__1;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__3;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11;
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__3;
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_SimpTheorems_eraseCore___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1;
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedOrigin___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__2;
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505_;
LEAN_EXPORT uint8_t l_Lean_Meta_instToFormatSimpTheorem___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableLtOrigin___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableLtOrigin(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableOrigin(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorem;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOrigin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__3;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__22;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isRflProofCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logWarning___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__1;
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__4;
static lean_object* l_Lean_Meta_isRflProofCore___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__2;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2178_(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__23;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLetDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpGlobalConfig___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__18;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__1;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__8;
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static size_t l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10;
static lean_object* l_Lean_Meta_instReprOrigin___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2;
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__8;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getSimpExtension_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2;
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7;
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__20;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__21;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__19;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3;
static lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___closed__1;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__18;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__17;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1;
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__4;
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__28;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_simpGlobalConfig;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1;
static lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__1;
static lean_object* l_Lean_Meta_simpGlobalConfig___closed__2;
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__1;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__9;
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isRflProofCore___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instLTOrigin;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2;
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isRflProofCore___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__6;
static lean_object* l_Lean_Meta_isRflProofCore___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__7;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isRflProofCore___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__25;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__13;
static uint64_t l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__17;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_ScopedEnvExtension_addCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3;
static lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin(lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__2;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_converse(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__24;
static lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpEntry___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Origin_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOrigin;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtensionMapRef;
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(lean_object*, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_instInhabitedExtensionState___spec__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___rarg___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__26;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__2;
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__16;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__14;
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8;
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__13;
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__12;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprOrigin;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedOrigin___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOrigin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedOrigin___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.decl", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.fvar", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__11;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.stx", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__14;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.other", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__17;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_nat_dec_le(x_6, x_2);
x_8 = l_Lean_Name_reprPrec(x_3, x_6);
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__3;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
if (x_7 == 0)
{
if (x_4 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
if (x_5 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = 0;
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = l_Repr_addAppParen(x_20, x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = 0;
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = l_Repr_addAppParen(x_27, x_2);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_11);
if (x_5 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6;
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = 0;
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = l_Repr_addAppParen(x_37, x_2);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_29);
x_40 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = 0;
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = l_Repr_addAppParen(x_43, x_2);
return x_44;
}
}
}
else
{
if (x_4 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6;
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_11);
if (x_5 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = 0;
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = l_Repr_addAppParen(x_52, x_2);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_54 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8;
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = 0;
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = l_Repr_addAppParen(x_59, x_2);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8;
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_11);
if (x_5 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_64 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6;
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_67 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = 0;
x_69 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = l_Repr_addAppParen(x_69, x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_61);
x_72 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = 0;
x_75 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = l_Repr_addAppParen(x_75, x_2);
return x_76;
}
}
}
}
case 1:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = lean_unsigned_to_nat(1024u);
x_79 = lean_nat_dec_le(x_78, x_2);
x_80 = l_Lean_Name_reprPrec(x_77, x_78);
x_81 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__12;
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
if (x_79 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_83 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_84 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = 0;
x_86 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = l_Repr_addAppParen(x_86, x_2);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_88 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_89 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
x_90 = 0;
x_91 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = l_Repr_addAppParen(x_91, x_2);
return x_92;
}
}
case 2:
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_1);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
x_96 = lean_unsigned_to_nat(1024u);
x_97 = lean_nat_dec_le(x_96, x_2);
x_98 = l_Lean_Name_reprPrec(x_94, x_96);
x_99 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_98);
lean_ctor_set(x_1, 0, x_99);
x_100 = lean_box(1);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2178_(x_95, x_96);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
if (x_97 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_104 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_105 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = 0;
x_107 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_106);
x_108 = l_Repr_addAppParen(x_107, x_2);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_109 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_110 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_103);
x_111 = 0;
x_112 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = l_Repr_addAppParen(x_112, x_2);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_114 = lean_ctor_get(x_1, 0);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_1);
x_116 = lean_unsigned_to_nat(1024u);
x_117 = lean_nat_dec_le(x_116, x_2);
x_118 = l_Lean_Name_reprPrec(x_114, x_116);
x_119 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15;
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_box(1);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2178_(x_115, x_116);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
if (x_117 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_126 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = 0;
x_128 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = l_Repr_addAppParen(x_128, x_2);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_130 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_131 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_124);
x_132 = 0;
x_133 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = l_Repr_addAppParen(x_133, x_2);
return x_134;
}
}
}
default: 
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
lean_dec(x_1);
x_136 = lean_unsigned_to_nat(1024u);
x_137 = lean_nat_dec_le(x_136, x_2);
x_138 = l_Lean_Name_reprPrec(x_135, x_136);
x_139 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__18;
x_140 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
if (x_137 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
x_141 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4;
x_142 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = 0;
x_144 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = l_Repr_addAppParen(x_144, x_2);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_146 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9;
x_147 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_140);
x_148 = 0;
x_149 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = l_Repr_addAppParen(x_149, x_2);
return x_150;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprOrigin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprOrigin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprOrigin___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Origin_key(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_converse(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 1, x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_6);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_14);
lean_dec(x_1);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOrigin(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
if (x_4 == 0)
{
if (x_6 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Meta_Origin_key(x_1);
x_14 = l_Lean_Meta_Origin_key(x_2);
x_15 = lean_name_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqOrigin(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableOrigin(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_2 == 0)
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash___override(x_3);
x_5 = 13;
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_Name_hash___override(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint64_t x_12; 
x_11 = l_Lean_Meta_Origin_key(x_1);
x_12 = l_Lean_Name_hash___override(x_11);
lean_dec(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instHashableOrigin(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Origin_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_7 = l_Lean_Name_lt(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_name_eq(x_3, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
if (x_4 == 0)
{
return x_6;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
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
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_Origin_key(x_1);
x_15 = l_Lean_Meta_Origin_key(x_2);
x_16 = l_Lean_Name_lt(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Origin_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instLTOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableLtOrigin(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Origin_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableLtOrigin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instDecidableLtOrigin(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedSimpTheorem___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l_Lean_Meta_instInhabitedSimpTheorem___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = 0;
x_5 = l_Lean_Meta_instInhabitedOrigin___closed__1;
x_6 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*5 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*5 + 2, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isRflProofCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isRflProofCore___closed__1;
x_2 = l_Lean_Meta_isRflProofCore___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isRflProofCore___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symm", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isRflProofCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isRflProofCore___closed__1;
x_2 = l_Lean_Meta_isRflProofCore___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_isRflProofCore___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_1, x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Meta_isRflProofCore___closed__4;
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Expr_isAppOfArity(x_2, x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Meta_isRflProofCore___closed__6;
x_22 = l_Lean_Expr_isAppOfArity(x_2, x_21, x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Meta_isRflProofCore___closed__8;
x_24 = lean_unsigned_to_nat(4u);
x_25 = l_Lean_Expr_isAppOfArity(x_2, x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_27 = l_Lean_Expr_isConst(x_26);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_constName_x21(x_26);
lean_dec(x_26);
x_32 = l_Lean_Meta_isRflTheorem(x_31, x_3, x_4, x_5);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_2 = x_33;
goto _start;
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_5);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_isRflProofCore(x_10, x_11, x_2, x_3, x_7);
lean_dec(x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_isRflProofCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isRflTheorem(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_isRflTheorem(x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_isRflProofCore(x_10, x_1, x_4, x_5, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instToFormatSimpTheorem___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instToFormatSimpTheorem___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":perm", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_5 = 1;
x_6 = l_Lean_Meta_instToFormatSimpTheorem___closed__1;
x_7 = l_Lean_Name_toString(x_4, x_5, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Meta_instToFormatSimpTheorem___closed__3;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_instToFormatSimpTheorem___closed__5;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
if (x_2 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Meta_instToFormatSimpTheorem___closed__7;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instToFormatSimpTheorem___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("↓ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("↓ ← ", 8, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
lean_dec(x_4);
x_8 = 0;
x_9 = l_Lean_MessageData_ofConstName(x_5, x_8);
if (x_6 == 0)
{
if (x_7 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_ppOrigin___rarg___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_apply_2(x_11, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Meta_ppOrigin___rarg___closed__5;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
x_21 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_apply_2(x_18, lean_box(0), x_22);
return x_23;
}
}
else
{
if (x_7 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_apply_2(x_25, lean_box(0), x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Meta_ppOrigin___rarg___closed__7;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
x_31 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_apply_2(x_28, lean_box(0), x_32);
return x_33;
}
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Expr_fvar___override(x_34);
x_38 = l_Lean_MessageData_ofExpr(x_37);
x_39 = lean_apply_2(x_36, lean_box(0), x_38);
return x_39;
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_MessageData_ofSyntax(x_40);
x_44 = lean_apply_2(x_42, lean_box(0), x_43);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
lean_dec(x_4);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_MessageData_ofName(x_45);
x_49 = lean_apply_2(x_47, lean_box(0), x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_ppOrigin___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_ppOrigin___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_2(x_13, lean_box(0), x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___closed__7;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Lean_Meta_ppSimpTheorem___rarg___lambda__2___closed__1;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_2(x_13, lean_box(0), x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Meta_ppOrigin___rarg(x_1, x_2, x_3, x_7);
if (x_5 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_ppSimpTheorem___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_ppSimpTheorem___rarg___lambda__2), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_ppSimpTheorem___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_ppSimpTheorem___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqSimpTheorem(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1;
x_3 = l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_instInhabitedExtensionState___spec__1;
x_4 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 2;
x_4 = 0;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_1);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_1);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_simpGlobalConfig___closed__1;
x_2 = l_Lean_Meta_Config_toConfigWithKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpGlobalConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint8_t x_10; 
x_7 = l_Lean_Meta_simpGlobalConfig;
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_8);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_9);
x_12 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 4);
x_26 = lean_ctor_get(x_2, 5);
x_27 = lean_ctor_get(x_2, 6);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set_uint64(x_30, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_30, sizeof(void*)*7 + 8, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*7 + 9, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*7 + 10, x_29);
x_31 = lean_apply_5(x_1, x_30, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withSimpGlobalConfig___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_7; lean_object* x_13; 
x_13 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_18 = lean_name_eq(x_14, x_16);
lean_dec(x_14);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 0;
x_7 = x_19;
goto block_12;
}
else
{
if (x_15 == 0)
{
if (x_17 == 0)
{
uint8_t x_20; 
x_20 = 1;
x_7 = x_20;
goto block_12;
}
else
{
uint8_t x_21; 
x_21 = 0;
x_7 = x_21;
goto block_12;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_22; 
x_22 = 0;
x_7 = x_22;
goto block_12;
}
else
{
uint8_t x_23; 
x_23 = 1;
x_7 = x_23;
goto block_12;
}
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_13);
x_24 = 0;
x_7 = x_24;
goto block_12;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_25; 
lean_dec(x_13);
x_25 = 0;
x_7 = x_25;
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Meta_Origin_key(x_13);
lean_dec(x_13);
x_27 = l_Lean_Meta_Origin_key(x_2);
x_28 = lean_name_eq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_7 = x_28;
goto block_12;
}
}
block_12:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_18 = lean_box(2);
x_19 = lean_array_get(x_18, x_4, x_8);
switch (lean_obj_tag(x_19)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_20, sizeof(void*)*1 + 1);
lean_dec(x_20);
x_25 = lean_name_eq(x_21, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 0;
x_9 = x_26;
goto block_17;
}
else
{
if (x_22 == 0)
{
if (x_24 == 0)
{
uint8_t x_27; 
x_27 = 1;
x_9 = x_27;
goto block_17;
}
else
{
uint8_t x_28; 
x_28 = 0;
x_9 = x_28;
goto block_17;
}
}
else
{
if (x_24 == 0)
{
uint8_t x_29; 
x_29 = 0;
x_9 = x_29;
goto block_17;
}
else
{
uint8_t x_30; 
x_30 = 1;
x_9 = x_30;
goto block_17;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_20);
x_31 = 0;
x_9 = x_31;
goto block_17;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_32);
x_33 = 0;
x_9 = x_33;
goto block_17;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Meta_Origin_key(x_3);
x_35 = l_Lean_Meta_Origin_key(x_32);
lean_dec(x_32);
x_36 = lean_name_eq(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_9 = x_36;
goto block_17;
}
}
}
case 1:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_array_set(x_4, x_8, x_18);
x_42 = lean_usize_shift_right(x_2, x_5);
x_43 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_40, x_42, x_3);
lean_inc(x_43);
x_44 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_ctor_set(x_19, 0, x_43);
x_45 = lean_array_set(x_41, x_8, x_19);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_43);
lean_free_object(x_19);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_array_set(x_41, x_8, x_46);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_set(x_41, x_8, x_51);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_52);
return x_1;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_array_set(x_4, x_8, x_18);
x_55 = lean_usize_shift_right(x_2, x_5);
x_56 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_53, x_55, x_3);
lean_inc(x_56);
x_57 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_array_set(x_54, x_8, x_58);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_59);
return x_1;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_56);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_set(x_54, x_8, x_64);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_67 = x_19;
} else {
 lean_dec_ref(x_19);
 x_67 = lean_box(0);
}
x_68 = lean_array_set(x_4, x_8, x_18);
x_69 = lean_usize_shift_right(x_2, x_5);
x_70 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_66, x_69, x_3);
lean_inc(x_70);
x_71 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_array_set(x_68, x_8, x_72);
lean_dec(x_8);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_70);
lean_dec(x_67);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_set(x_68, x_8, x_79);
lean_dec(x_8);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
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
block_17:
{
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_box(2);
x_13 = lean_array_set(x_4, x_8, x_12);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_box(2);
x_15 = lean_array_set(x_4, x_8, x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Array_idxOfAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__3(x_82, x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_83);
lean_dec(x_82);
return x_1;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_1);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_1, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_1, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
lean_dec(x_85);
lean_inc(x_89);
x_90 = l_Array_eraseIdx___rarg(x_82, x_89, lean_box(0));
x_91 = l_Array_eraseIdx___rarg(x_83, x_89, lean_box(0));
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_90);
return x_1;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
lean_dec(x_85);
lean_inc(x_92);
x_93 = l_Array_eraseIdx___rarg(x_82, x_92, lean_box(0));
x_94 = l_Array_eraseIdx___rarg(x_83, x_92, lean_box(0));
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_3 == 0)
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_hash___override(x_4);
x_6 = 13;
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_1, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Lean_Name_hash___override(x_10);
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_1, x_14, x_2);
return x_15;
}
}
else
{
lean_object* x_16; uint64_t x_17; size_t x_18; lean_object* x_19; 
x_16 = l_Lean_Meta_Origin_key(x_2);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_1, x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*1 + 1);
if (x_17 == 0)
{
lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = 13;
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_shift_right(x_22, x_14);
x_24 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_6, x_23, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
x_27 = l_Lean_Name_hash___override(x_26);
lean_dec(x_26);
x_28 = 11;
x_29 = lean_uint64_mix_hash(x_27, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_shift_right(x_30, x_14);
x_32 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_6, x_31, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_34 = l_Lean_Meta_Origin_key(x_9);
x_35 = l_Lean_Name_hash___override(x_34);
lean_dec(x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_shift_right(x_36, x_14);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_6, x_37, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_38;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t x_17; lean_object* x_30; 
x_30 = lean_array_fget(x_5, x_2);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
lean_dec(x_30);
x_35 = lean_name_eq(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 0;
x_17 = x_36;
goto block_29;
}
else
{
if (x_32 == 0)
{
if (x_34 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_17 = x_37;
goto block_29;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_17 = x_38;
goto block_29;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_17 = x_39;
goto block_29;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_17 = x_40;
goto block_29;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_30);
x_41 = 0;
x_17 = x_41;
goto block_29;
}
}
else
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_42; 
lean_dec(x_30);
x_42 = 0;
x_17 = x_42;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Meta_Origin_key(x_3);
x_44 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_45 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_17 = x_45;
goto block_29;
}
}
block_29:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = lean_array_fset(x_5, x_2, x_3);
x_27 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_7;
}
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_6, x_12);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_12, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_21 = x_16;
} else {
 lean_dec_ref(x_16);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
x_35 = lean_name_eq(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 0;
x_22 = x_36;
goto block_30;
}
else
{
if (x_32 == 0)
{
if (x_34 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_22 = x_37;
goto block_30;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_22 = x_38;
goto block_30;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_22 = x_39;
goto block_30;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_22 = x_40;
goto block_30;
}
}
}
}
else
{
uint8_t x_41; 
x_41 = 0;
x_22 = x_41;
goto block_30;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_42; 
x_42 = 0;
x_22 = x_42;
goto block_30;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Meta_Origin_key(x_4);
x_44 = l_Lean_Meta_Origin_key(x_19);
x_45 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_22 = x_45;
goto block_30;
}
}
block_30:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_23 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_12, x_24);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_7;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_19);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
x_28 = lean_array_fset(x_18, x_12, x_27);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_7;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
case 1:
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_usize_shift_right(x_2, x_9);
x_49 = lean_usize_add(x_3, x_8);
x_50 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_47, x_48, x_49, x_4, x_5);
lean_ctor_set(x_16, 0, x_50);
x_51 = lean_array_fset(x_18, x_12, x_16);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_7;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
x_54 = lean_usize_shift_right(x_2, x_9);
x_55 = lean_usize_add(x_3, x_8);
x_56 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_53, x_54, x_55, x_4, x_5);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_array_fset(x_18, x_12, x_57);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_7;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_5);
x_61 = lean_array_fset(x_18, x_12, x_60);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_7;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; size_t x_66; uint8_t x_67; 
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__7(x_1, x_64, x_4, x_5);
x_66 = 7;
x_67 = lean_usize_dec_le(x_66, x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_65);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_dec_lt(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_dec(x_65);
x_73 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1;
x_74 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6(x_3, x_71, x_72, lean_box(0), x_64, x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_74;
}
else
{
return x_65;
}
}
else
{
return x_65;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_1, 0);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_1);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__7(x_77, x_78, x_4, x_5);
x_80 = 7;
x_81 = lean_usize_dec_le(x_80, x_3);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_79);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_dec_lt(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1;
x_88 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6(x_3, x_85, x_86, lean_box(0), x_78, x_87);
lean_dec(x_86);
lean_dec(x_85);
return x_88;
}
else
{
return x_79;
}
}
else
{
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_SimpTheorems_eraseCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; 
x_4 = 1;
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_8 = 13;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_1, x_10, x_4, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_Lean_Name_hash___override(x_12);
lean_dec(x_12);
x_14 = 11;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_1, x_16, x_4, x_2, x_3);
return x_17;
}
}
else
{
lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; 
x_18 = l_Lean_Meta_Origin_key(x_2);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_1, x_20, x_4, x_2, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_8);
x_10 = l_Lean_Meta_SimpTheorems_eraseCore(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_6, x_2);
x_11 = lean_box(0);
lean_inc(x_2);
x_12 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_SimpTheorems_eraseCore___spec__4(x_8, x_2, x_11);
lean_inc(x_9);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_ctor_set(x_1, 4, x_12);
lean_ctor_set(x_1, 2, x_10);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(x_7, x_13);
lean_inc(x_9);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set(x_15, 5, x_9);
x_16 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___spec__1(x_9, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
return x_15;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
return x_15;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8(x_17, x_22, x_23, x_15);
lean_dec(x_17);
return x_24;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get(x_1, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_31 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_27, x_2);
x_32 = lean_box(0);
lean_inc(x_2);
x_33 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_SimpTheorems_eraseCore___spec__4(x_29, x_2, x_32);
lean_inc(x_30);
lean_inc(x_33);
lean_inc(x_28);
lean_inc(x_31);
lean_inc(x_26);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_30);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_PersistentHashMap_erase___at_Lean_KeyedDeclsAttribute_ExtensionState_insert___spec__1(x_28, x_35);
lean_inc(x_30);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_30);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___spec__1(x_30, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_38) == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_array_get_size(x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
return x_37;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
return x_37;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8(x_39, x_44, x_45, x_37);
lean_dec(x_39);
return x_46;
}
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_SimpTheorems_eraseCore___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_eraseCore___spec__8(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fget(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_dec(x_15);
x_20 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
x_6 = x_21;
goto block_11;
}
else
{
if (x_17 == 0)
{
if (x_19 == 0)
{
uint8_t x_22; 
x_22 = 1;
x_6 = x_22;
goto block_11;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_6 = x_23;
goto block_11;
}
}
else
{
if (x_19 == 0)
{
uint8_t x_24; 
x_24 = 0;
x_6 = x_24;
goto block_11;
}
else
{
uint8_t x_25; 
x_25 = 1;
x_6 = x_25;
goto block_11;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = 0;
x_6 = x_26;
goto block_11;
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_27; 
lean_dec(x_15);
x_27 = 0;
x_6 = x_27;
goto block_11;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Meta_Origin_key(x_5);
x_29 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_30 = lean_name_eq(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_6 = x_30;
goto block_11;
}
}
}
block_11:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 1);
lean_dec(x_11);
x_16 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
if (x_13 == 0)
{
if (x_15 == 0)
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
else
{
return x_15;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = 0;
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_21);
x_22 = 0;
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Meta_Origin_key(x_3);
x_24 = l_Lean_Meta_Origin_key(x_21);
lean_dec(x_21);
x_25 = lean_name_eq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; size_t x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_usize_shift_right(x_2, x_5);
x_1 = x_26;
x_2 = x_27;
goto _start;
}
default: 
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__3(x_30, x_31, lean_box(0), x_32, x_3);
lean_dec(x_31);
lean_dec(x_30);
return x_33;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_3 == 0)
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_hash___override(x_4);
x_6 = 13;
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2(x_1, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Lean_Name_hash___override(x_10);
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2(x_1, x_14, x_2);
return x_15;
}
}
else
{
lean_object* x_16; uint64_t x_17; size_t x_18; uint8_t x_19; 
x_16 = l_Lean_Meta_Origin_key(x_2);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2(x_1, x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_Origin_converse(x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_SimpTheorems_eraseCore___spec__4(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_5, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
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
x_14 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_3, x_12);
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
x_22 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
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
x_29 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_3, x_27);
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
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_3, x_17);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
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
x_21 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_4, x_19);
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
x_28 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_4, x_26);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
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
x_63 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_4, x_60);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(x_1, x_83, x_4, x_5);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_addSimpTheoremEntry___spec__8(x_96, x_97, x_4, x_5);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_addSimpTheoremEntry___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = lean_array_push(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_expr_eqv(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_nat_add(x_7, x_8);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_fget(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 0);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = l_Lean_Meta_DiscrTree_Key_lt(x_16, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_13, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_box(0);
x_22 = lean_array_fset(x_5, x_13, x_21);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_27, x_24);
lean_dec(x_27);
lean_ctor_set(x_14, 1, x_28);
lean_ctor_set(x_14, 0, x_4);
x_29 = lean_array_fset(x_22, x_13, x_14);
lean_dec(x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_3, x_31);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_32, x_30);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_fset(x_22, x_13, x_34);
lean_dec(x_13);
return x_35;
}
}
}
else
{
lean_dec(x_14);
x_8 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = lean_nat_dec_eq(x_13, x_7);
if (x_37 == 0)
{
lean_dec(x_7);
x_7 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_8);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
x_44 = lean_array_get_size(x_5);
x_45 = lean_array_push(x_5, x_42);
x_46 = l_Array_insertIdx_loop___rarg(x_43, x_45, x_44);
lean_dec(x_43);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_5, x_8);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_11);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_box(0);
x_17 = lean_array_fset(x_5, x_8, x_16);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_22, x_19);
lean_dec(x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_4);
x_24 = lean_array_fset(x_17, x_8, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_27, x_25);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_fset(x_17, x_8, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_10);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_7, x_31);
x_33 = lean_array_fget(x_5, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_nat_dec_lt(x_32, x_7);
lean_dec(x_7);
if (x_37 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_box(0);
x_39 = lean_array_fset(x_5, x_32, x_38);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_33, 1);
x_42 = lean_ctor_get(x_33, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_3, x_31);
x_44 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_43, x_41);
lean_dec(x_43);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_4);
x_45 = lean_array_fset(x_39, x_32, x_33);
lean_dec(x_32);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_nat_add(x_3, x_31);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_47, x_46);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_fset(x_39, x_32, x_49);
lean_dec(x_32);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_7);
x_51 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_32, lean_box(0), lean_box(0));
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
x_52 = lean_nat_add(x_3, x_31);
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_5, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_10);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_3, x_56);
x_58 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_5, x_59);
x_61 = l_Array_insertIdx_loop___rarg(x_8, x_60, x_7);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_7);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_3, x_62);
x_64 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_5, x_65);
return x_66;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_addSimpTheoremEntry___spec__10(x_6, x_2, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_1, x_3);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11(x_1, x_2, x_3, x_12, x_7, x_14);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_3, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_addSimpTheoremEntry___spec__10(x_16, x_2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_array_fget(x_1, x_3);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11(x_1, x_2, x_3, x_23, x_17, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.insertCore", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid key sequence", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(482u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_9);
x_11 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(x_1, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_2, x_3, x_13, x_12);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_addSimpTheoremEntry___spec__5(x_1, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4;
x_17 = l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_2);
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(x_1, x_2);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_inc(x_2);
x_9 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_6, x_8, x_2);
lean_dec(x_8);
x_10 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_7);
lean_ctor_set(x_3, 2, x_10);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_inc(x_2);
x_18 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_11, x_17, x_2);
lean_dec(x_17);
x_19 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_13);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_inc(x_2);
x_25 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_22, x_24, x_2);
lean_dec(x_24);
x_26 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_23);
lean_ctor_set(x_3, 2, x_26);
lean_ctor_set(x_3, 1, x_25);
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_3, 2);
x_30 = lean_ctor_get(x_3, 3);
x_31 = lean_ctor_get(x_3, 4);
x_32 = lean_ctor_get(x_3, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_inc(x_2);
x_34 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_28, x_33, x_2);
lean_dec(x_33);
x_35 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_29);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_30);
lean_ctor_set(x_36, 4, x_31);
lean_ctor_set(x_36, 5, x_32);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_addSimpTheoremEntry___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_addSimpTheoremEntry___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_addSimpTheoremEntry___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_addSimpTheoremEntry___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__6(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpTheoremEntry___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binInsertM___at_Lean_Meta_addSimpTheoremEntry___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_4, x_2, x_5);
lean_ctor_set(x_1, 3, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_10, x_2, x_13);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_4, x_2, x_5);
lean_ctor_set(x_1, 3, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_10, x_2, x_13);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLetDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 5);
x_6 = l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(x_5, x_2, x_3);
lean_ctor_set(x_1, 5, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(x_12, x_2, x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_13);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2;
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
x_20 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_Meta_Origin_key(x_2);
x_10 = l_Lean_MessageData_ofName(x_9);
x_11 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_1);
x_15 = l_Lean_logWarning___rarg(x_1, x_3, x_4, x_5, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_6);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
lean_closure_set(x_8, 5, x_6);
x_9 = l_Lean_Meta_Origin_converse(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_8);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
lean_inc(x_6);
x_17 = l_Lean_Meta_SimpTheorems_isLemma(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_22, x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_16);
x_27 = lean_apply_2(x_25, lean_box(0), x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_13; lean_object* x_14; uint8_t x_22; 
lean_inc(x_5);
lean_inc(x_6);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_inc(x_5);
x_22 = l_Lean_Meta_SimpTheorems_isLemma(x_5, x_6);
if (x_22 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_inc(x_5);
x_24 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_5, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_5, 5);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_25, x_23);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_box(0);
x_14 = x_27;
goto block_21;
}
else
{
lean_object* x_28; 
lean_dec(x_13);
x_28 = lean_box(0);
x_7 = x_28;
goto block_12;
}
}
else
{
lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_13);
x_29 = lean_box(0);
x_7 = x_29;
goto block_12;
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_box(0);
x_14 = x_30;
goto block_21;
}
}
else
{
lean_object* x_31; 
lean_dec(x_13);
x_31 = lean_box(0);
x_7 = x_31;
goto block_12;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_SimpTheorems_eraseCore(x_5, x_6);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_SimpTheorems_erase___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_SimpTheorems_erase___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_erase___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = lean_expr_instantiate1(x_2, x_3);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
default: 
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_14, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_19);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_1 = x_15;
x_2 = x_17;
x_7 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
case 10:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_2 = x_31;
goto _start;
}
default: 
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_37);
x_41 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_37, x_39, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1___boxed), 8, 2);
lean_closure_set(x_49, 0, x_38);
lean_closure_set(x_49, 1, x_40);
x_50 = 0;
x_51 = 0;
x_52 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(x_36, x_50, x_37, x_49, x_51, x_3, x_4, x_5, x_6, x_48);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_41);
if (x_53 == 0)
{
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 10:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_dec(x_2);
x_2 = x_57;
goto _start;
}
default: 
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_63);
x_67 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_63, x_65, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_67, 0);
lean_dec(x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; 
lean_dec(x_68);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_dec(x_67);
x_75 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1___boxed), 8, 2);
lean_closure_set(x_75, 0, x_64);
lean_closure_set(x_75, 1, x_66);
x_76 = 0;
x_77 = 0;
x_78 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(x_62, x_76, x_63, x_75, x_77, x_3, x_4, x_5, x_6, x_74);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_67);
if (x_79 == 0)
{
return x_67;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_67, 0);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_67);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_2 = x_83;
goto _start;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_7);
return x_87;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 8:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 3);
lean_inc(x_91);
lean_dec(x_1);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 3);
lean_inc(x_94);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_89);
x_95 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_89, x_92, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
if (x_97 == 0)
{
uint8_t x_98; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_95, 0);
lean_dec(x_99);
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec(x_95);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_90);
x_103 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_90, x_93, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_103, 0);
lean_dec(x_107);
return x_103;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
lean_dec(x_104);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1___boxed), 8, 2);
lean_closure_set(x_111, 0, x_91);
lean_closure_set(x_111, 1, x_94);
x_112 = 0;
x_113 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_88, x_89, x_90, x_111, x_112, x_3, x_4, x_5, x_6, x_110);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_103);
if (x_114 == 0)
{
return x_103;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_103, 0);
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_103);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_95);
if (x_118 == 0)
{
return x_95;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_95, 0);
x_120 = lean_ctor_get(x_95, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_95);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
case 10:
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_122);
lean_dec(x_2);
x_2 = x_122;
goto _start;
}
default: 
{
uint8_t x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_box(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_7);
return x_126;
}
}
}
case 10:
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_1, 1);
lean_inc(x_127);
lean_dec(x_1);
x_1 = x_127;
goto _start;
}
case 11:
{
switch (lean_obj_tag(x_2)) {
case 10:
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
lean_dec(x_2);
x_2 = x_129;
goto _start;
}
case 11:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_131 = lean_ctor_get(x_1, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 2);
lean_inc(x_132);
lean_dec(x_1);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 2);
lean_inc(x_134);
lean_dec(x_2);
x_135 = lean_nat_dec_eq(x_131, x_133);
lean_dec(x_133);
lean_dec(x_131);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_7);
return x_137;
}
else
{
x_1 = x_132;
x_2 = x_134;
goto _start;
}
}
default: 
{
uint8_t x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_box(x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_7);
return x_141;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_2, 1);
lean_inc(x_142);
lean_dec(x_2);
x_2 = x_142;
goto _start;
}
else
{
uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_box(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_7);
return x_146;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid `simp` theorem, equation is equivalent to", 49, 49);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_8 = l_Lean_Meta_simpGlobalConfig;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 6);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_20 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set_uint64(x_20, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 10, x_19);
x_21 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_DiscrTree_reduceDT(x_1, x_21, x_20, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_expr_eqv(x_24, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Expr_isFVar(x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_object* x_30; 
lean_free_object(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Meta_mkEq(x_24, x_2, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_indentExpr(x_31);
x_34 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_37, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_expr_eqv(x_43, x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isFVar(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
else
{
lean_object* x_51; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_mkEq(x_43, x_2, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_indentExpr(x_52);
x_55 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_58, x_3, x_4, x_5, x_6, x_53);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_62 = x_51;
} else {
 lean_dec_ref(x_51);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_isRflProofCore___closed__2;
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_2, x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_2);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_2);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_15, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
x_8 = 0;
x_9 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_List_reverse___rarg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = 0;
x_18 = 1;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_1, x_15, x_17, x_18, x_17, x_19, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_mkForallFVars(x_1, x_16, x_17, x_18, x_19, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_21);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_14;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_25;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_21);
lean_free_object(x_12);
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_3);
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
lean_free_object(x_12);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_3);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = 0;
x_39 = 1;
x_40 = 1;
x_41 = l_Lean_Meta_mkLambdaFVars(x_1, x_36, x_38, x_39, x_38, x_40, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_mkForallFVars(x_1, x_37, x_38, x_39, x_40, x_4, x_5, x_6, x_7, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_47);
{
lean_object* _tmp_1 = x_35;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_46;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_3);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_3);
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_55 = x_41;
} else {
 lean_dec_ref(x_41);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_2);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = 0;
x_63 = 1;
x_64 = 1;
x_65 = l_Lean_Meta_mkLambdaFVars(x_1, x_59, x_62, x_63, x_62, x_64, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_mkForallFVars(x_1, x_60, x_62, x_63, x_64, x_4, x_5, x_6, x_7, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
if (lean_is_scalar(x_61)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
x_2 = x_58;
x_3 = x_72;
x_8 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_3);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_3);
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_mkEq(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEqTrue(x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
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
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_mkEq(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEqFalse(x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
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
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_eq_false", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_eq_true", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(x_1, x_2, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3;
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(x_1, x_2, x_21, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_mk(x_24);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_mkAppM(x_26, x_25, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
x_31 = l_Lean_Meta_mkEq(x_15, x_30, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_28);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_16);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_mk(x_50);
x_52 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l_Lean_Meta_mkAppM(x_52, x_51, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_57 = l_Lean_Meta_mkEq(x_15, x_56, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_49);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_54);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_53);
if (x_71 == 0)
{
return x_53;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_53, 0);
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_53);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_mkEq(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_mkEq(x_11, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkEqFalse(x_3, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2;
x_11 = l_Lean_Expr_isConstOf(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3;
x_13 = l_Lean_Expr_isConstOf(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_mk(x_17);
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_mkAppM(x_19, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6;
x_24 = l_Lean_Meta_mkEq(x_1, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_21);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_mk(x_43);
x_45 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Lean_Meta_mkAppM(x_45, x_44, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9;
x_50 = l_Lean_Meta_mkEq(x_1, x_49, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_47);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_46);
if (x_64 == 0)
{
return x_46;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_46, 0);
x_66 = lean_ctor_get(x_46, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_46);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_mkEq(x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkPropExt(x_4, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_12);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_34 = l_Lean_Meta_mkEq(x_3, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Meta_mkPropExt(x_4, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_mkEqSymm(x_38, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_35);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_35);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
return x_37;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_37);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_34);
if (x_60 == 0)
{
return x_34;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_mkEq(x_4, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkEqSymm(x_2, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_17);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkAppN(x_1, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_List_mapM_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_4, x_13, x_15, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'True'", 48, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'False'", 49, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_whnf(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_isRflProofCore___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_11, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2;
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Expr_isAppOfArity(x_11, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4;
x_21 = l_Lean_Expr_isAppOfArity(x_11, x_20, x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6;
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Expr_isAppOfArity(x_11, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8;
x_26 = l_Lean_Expr_isAppOfArity(x_11, x_25, x_18);
if (x_26 == 0)
{
if (x_1 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(x_11, x_3, x_27, x_5, x_6, x_7, x_8, x_12);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_3);
x_29 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10;
x_30 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_29, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = l_Lean_Expr_appFn_x21(x_11);
x_36 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_37 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_38 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_39 = l_Lean_Expr_proj___override(x_25, x_38, x_3);
x_40 = l_Lean_Expr_proj___override(x_25, x_23, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_39, x_36, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_40, x_37, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l_List_appendTR___rarg(x_42, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = l_List_appendTR___rarg(x_42, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_42);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
return x_41;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; 
x_60 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
x_62 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(x_60, x_3, x_14, x_61, x_5, x_6, x_7, x_8, x_12);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
lean_dec(x_3);
x_63 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
x_64 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_63, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = l_Lean_Expr_appFn_x21(x_11);
x_70 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_71 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(x_70, x_71, x_3, x_72, x_5, x_6, x_7, x_8, x_12);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_3);
x_74 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
x_75 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_74, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = l_Lean_Expr_appFn_x21(x_11);
x_81 = l_Lean_Expr_appArg_x21(x_80);
lean_dec(x_80);
x_82 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_2 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_box(0);
x_84 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(x_1, x_81, x_82, x_3, x_83, x_5, x_6, x_7, x_8, x_12);
return x_84;
}
else
{
lean_object* x_85; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_82);
lean_inc(x_81);
x_85 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_81, x_82, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(x_1, x_81, x_82, x_3, x_86, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_86);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = l_Lean_Expr_appFn_x21(x_11);
x_94 = l_Lean_Expr_appArg_x21(x_93);
lean_dec(x_93);
x_95 = l_Lean_Expr_appArg_x21(x_11);
if (x_2 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_box(0);
x_97 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(x_1, x_3, x_11, x_95, x_94, x_96, x_5, x_6, x_7, x_8, x_12);
return x_97;
}
else
{
lean_object* x_98; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_95);
lean_inc(x_94);
x_98 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_94, x_95, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(x_1, x_3, x_11, x_95, x_94, x_99, x_5, x_6, x_7, x_8, x_100);
lean_dec(x_99);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
return x_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_98);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_106 = lean_box(x_1);
x_107 = lean_box(x_2);
x_108 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8___boxed), 10, 3);
lean_closure_set(x_108, 0, x_3);
lean_closure_set(x_108, 1, x_106);
lean_closure_set(x_108, 2, x_107);
x_109 = 0;
x_110 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_11, x_108, x_109, x_5, x_6, x_7, x_8, x_12);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_10);
if (x_111 == 0)
{
return x_10;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_10, 0);
x_113 = lean_ctor_get(x_10, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_10);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__6(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__7(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_4, x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'simp', proposition expected", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_indentExpr(x_1);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_14 = l_Lean_Meta_isRflProof(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_12);
x_17 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_1);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_4);
x_18 = lean_unbox(x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_18);
x_19 = lean_unbox(x_16);
lean_dec(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 2, x_19);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
lean_inc(x_12);
x_22 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_1);
lean_ctor_set(x_22, 3, x_3);
lean_ctor_set(x_22, 4, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_4);
x_23 = lean_unbox(x_13);
lean_ctor_set_uint8(x_22, sizeof(void*)*5 + 1, x_23);
x_24 = lean_unbox(x_20);
lean_dec(x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5 + 2, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected kind of 'simp' theorem", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_14, x_2, x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Meta_whnfR(x_23, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_isRflProofCore___closed__2;
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Expr_isAppOfArity(x_26, x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = l_Lean_indentExpr(x_26);
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_31);
lean_ctor_set(x_17, 0, x_32);
x_33 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_34, x_9, x_10, x_11, x_12, x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_17);
x_40 = l_Lean_Expr_appFn_x21(x_26);
x_41 = l_Lean_Expr_appArg_x21(x_40);
lean_dec(x_40);
x_42 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
x_43 = l_Lean_Meta_DiscrTree_mkPath(x_41, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_46 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_41, x_42, x_9, x_10, x_11, x_12, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_ctor_set(x_19, 1, x_47);
lean_ctor_set(x_19, 0, x_44);
x_49 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_48);
lean_dec(x_19);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_44);
lean_free_object(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_25);
if (x_58 == 0)
{
return x_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_63 = l_Lean_Meta_whnfR(x_62, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Meta_isRflProofCore___closed__2;
x_67 = lean_unsigned_to_nat(3u);
x_68 = l_Lean_Expr_isAppOfArity(x_64, x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = l_Lean_indentExpr(x_64);
x_70 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_69);
lean_ctor_set(x_17, 0, x_70);
x_71 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_72, x_9, x_10, x_11, x_12, x_65);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_17);
x_78 = l_Lean_Expr_appFn_x21(x_64);
x_79 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
x_80 = l_Lean_Expr_appArg_x21(x_64);
lean_dec(x_64);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_79);
x_81 = l_Lean_Meta_DiscrTree_mkPath(x_79, x_8, x_9, x_10, x_11, x_12, x_65);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_84 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_79, x_80, x_9, x_10, x_11, x_12, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_85);
x_88 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_87, x_9, x_10, x_11, x_12, x_86);
lean_dec(x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_81, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_95 = x_81;
} else {
 lean_dec_ref(x_81);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = lean_ctor_get(x_63, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_63, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_99 = x_63;
} else {
 lean_dec_ref(x_63);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_17, 1);
lean_inc(x_101);
lean_dec(x_17);
x_102 = lean_ctor_get(x_16, 1);
lean_inc(x_102);
lean_dec(x_16);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_105 = l_Lean_Meta_whnfR(x_103, x_9, x_10, x_11, x_12, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_isRflProofCore___closed__2;
x_109 = lean_unsigned_to_nat(3u);
x_110 = l_Lean_Expr_isAppOfArity(x_106, x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = l_Lean_indentExpr(x_106);
x_112 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Meta_ppOrigin___rarg___closed__3;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_115, x_9, x_10, x_11, x_12, x_107);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = l_Lean_Expr_appFn_x21(x_106);
x_122 = l_Lean_Expr_appArg_x21(x_121);
lean_dec(x_121);
x_123 = l_Lean_Expr_appArg_x21(x_106);
lean_dec(x_106);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_122);
x_124 = l_Lean_Meta_DiscrTree_mkPath(x_122, x_8, x_9, x_10, x_11, x_12, x_107);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_127 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_122, x_123, x_9, x_10, x_11, x_12, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
if (lean_is_scalar(x_104)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_104;
}
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_128);
x_131 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_130, x_9, x_10, x_11, x_12, x_129);
lean_dec(x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
lean_dec(x_104);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_104);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_124, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_138 = x_124;
} else {
 lean_dec_ref(x_124);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_104);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_ctor_get(x_105, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_105, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_142 = x_105;
} else {
 lean_dec_ref(x_105);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = !lean_is_exclusive(x_16);
if (x_144 == 0)
{
return x_16;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_16, 0);
x_146 = lean_ctor_get(x_16, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_16);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1;
x_2 = l_Lean_Meta_Origin_key(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin != .fvar ⟨.anonymous⟩\n  ", 35, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.SimpTheorems", 34, 34);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Simp.SimpTheorems.0.Lean.Meta.mkSimpTheoremCore", 73, 73);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__7;
x_3 = lean_unsigned_to_nat(391u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_13 = x_31;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Meta_Origin_key(x_1);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2;
x_34 = lean_name_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_13 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__8;
x_37 = l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2(x_36, x_8, x_9, x_10, x_11, x_12);
return x_37;
}
}
block_30:
{
lean_object* x_14; 
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = lean_infer_type(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_15, x_8, x_9, x_10, x_11, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_box(x_5);
x_22 = lean_box(x_7);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___boxed), 13, 8);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_4);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_6);
lean_closure_set(x_23, 5, x_21);
lean_closure_set(x_23, 6, x_1);
lean_closure_set(x_23, 7, x_22);
x_24 = 0;
x_25 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_23, x_24, x_8, x_9, x_10, x_11, x_19);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_2, x_3, x_4, x_13, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
x_23 = l_Lean_Meta_mkAuxLemma(x_3, x_22, x_21, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_5);
lean_inc(x_24);
x_26 = l_Lean_Expr_const___override(x_24, x_5);
lean_inc(x_4);
x_27 = l_Lean_Expr_const___override(x_24, x_4);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_29 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_6);
x_30 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_6, x_26, x_28, x_27, x_1, x_2, x_29, x_13, x_14, x_15, x_16, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_11, x_31);
x_10 = x_20;
x_11 = x_33;
x_12 = lean_box(0);
x_17 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_levelParams(x_11);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_3);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Expr_const___override(x_1, x_15);
x_18 = l_Lean_Meta_simpGlobalConfig;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_18, sizeof(void*)*1);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_5, 0);
lean_dec(x_22);
lean_ctor_set(x_5, 0, x_19);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_23 = lean_infer_type(x_17, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_24, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
x_29 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_30 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_24, x_28, x_29, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
if (x_3 == 0)
{
uint8_t x_54; 
x_54 = lean_unbox(x_31);
lean_dec(x_31);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_13);
x_55 = l_Lean_Expr_const___override(x_1, x_14);
x_56 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_57 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_16, x_17, x_56, x_55, x_2, x_4, x_29, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
x_61 = lean_array_mk(x_60);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_14);
x_65 = lean_array_mk(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_1);
x_71 = lean_box(0);
x_33 = x_71;
goto block_53;
}
}
else
{
lean_object* x_72; 
lean_dec(x_31);
lean_dec(x_1);
x_72 = lean_box(0);
x_33 = x_72;
goto block_53;
}
block_53:
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_33);
x_34 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_34, x_17, x_24, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
lean_inc(x_36);
x_40 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_2, x_4, x_13, x_14, x_15, x_16, x_36, x_38, x_36, x_36, x_39, lean_box(0), x_5, x_6, x_7, x_8, x_37);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_30);
if (x_73 == 0)
{
return x_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_30, 0);
x_75 = lean_ctor_get(x_30, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_30);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_26);
if (x_77 == 0)
{
return x_26;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_26, 0);
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_26);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_23);
if (x_81 == 0)
{
return x_23;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_23, 0);
x_83 = lean_ctor_get(x_23, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_23);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_86 = lean_ctor_get(x_5, 1);
x_87 = lean_ctor_get(x_5, 2);
x_88 = lean_ctor_get(x_5, 3);
x_89 = lean_ctor_get(x_5, 4);
x_90 = lean_ctor_get(x_5, 5);
x_91 = lean_ctor_get(x_5, 6);
x_92 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_93 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_5);
x_94 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_94, 0, x_19);
lean_ctor_set(x_94, 1, x_86);
lean_ctor_set(x_94, 2, x_87);
lean_ctor_set(x_94, 3, x_88);
lean_ctor_set(x_94, 4, x_89);
lean_ctor_set(x_94, 5, x_90);
lean_ctor_set(x_94, 6, x_91);
lean_ctor_set_uint64(x_94, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 8, x_85);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 9, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 10, x_93);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_94);
lean_inc(x_17);
x_95 = lean_infer_type(x_17, x_94, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_94);
lean_inc(x_96);
x_98 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_96, x_94, x_6, x_7, x_8, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1;
x_101 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_94);
lean_inc(x_96);
x_102 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_96, x_100, x_101, x_94, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
if (x_3 == 0)
{
uint8_t x_126; 
x_126 = lean_unbox(x_103);
lean_dec(x_103);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_96);
lean_dec(x_15);
lean_dec(x_13);
x_127 = l_Lean_Expr_const___override(x_1, x_14);
x_128 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_129 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_16, x_17, x_128, x_127, x_2, x_4, x_101, x_94, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_14);
x_134 = lean_array_mk(x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; 
lean_dec(x_1);
x_140 = lean_box(0);
x_105 = x_140;
goto block_125;
}
}
else
{
lean_object* x_141; 
lean_dec(x_103);
lean_dec(x_1);
x_141 = lean_box(0);
x_105 = x_141;
goto block_125;
}
block_125:
{
uint8_t x_106; lean_object* x_107; 
lean_dec(x_105);
x_106 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_94);
x_107 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_106, x_17, x_96, x_94, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_box(0);
x_111 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
lean_inc(x_108);
x_112 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_2, x_4, x_13, x_14, x_15, x_16, x_108, x_110, x_108, x_108, x_111, lean_box(0), x_94, x_6, x_7, x_8, x_109);
lean_dec(x_108);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_94);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_121 = lean_ctor_get(x_107, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_107, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_123 = x_107;
} else {
 lean_dec_ref(x_107);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_142 = lean_ctor_get(x_102, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_102, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_144 = x_102;
} else {
 lean_dec_ref(x_102);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_146 = lean_ctor_get(x_98, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_98, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_148 = x_98;
} else {
 lean_dec_ref(x_98);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_94);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_150 = lean_ctor_get(x_95, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_95, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_152 = x_95;
} else {
 lean_dec_ref(x_95);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_10);
if (x_154 == 0)
{
return x_10;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_10, 0);
x_156 = lean_ctor_get(x_10, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_10);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_instInhabitedSimpTheorems;
x_10 = l_Lean_ScopedEnvExtension_getState___rarg(x_9, x_1, x_8);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_instInhabitedSimpTheorems;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_14, x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 6);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_ref_take(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 4);
lean_dec(x_15);
x_16 = l_Lean_ScopedEnvExtension_addCore___rarg(x_14, x_1, x_2, x_3, x_9);
x_17 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
lean_ctor_set(x_11, 4, x_17);
lean_ctor_set(x_11, 0, x_16);
x_18 = lean_st_ref_set(x_7, x_11, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2;
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_5, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_22);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
x_46 = lean_ctor_get(x_11, 2);
x_47 = lean_ctor_get(x_11, 3);
x_48 = lean_ctor_get(x_11, 5);
x_49 = lean_ctor_get(x_11, 6);
x_50 = lean_ctor_get(x_11, 7);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_51 = l_Lean_ScopedEnvExtension_addCore___rarg(x_44, x_1, x_2, x_3, x_9);
x_52 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1;
x_53 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_48);
lean_ctor_set(x_53, 6, x_49);
lean_ctor_set(x_53, 7, x_50);
x_54 = lean_st_ref_set(x_7, x_53, x_12);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_5, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 4);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
x_64 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
x_66 = lean_st_ref_set(x_5, x_65, x_58);
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
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_11);
lean_inc(x_1);
x_18 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_17, x_2, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_22 = lean_box(0);
x_7 = x_21;
x_8 = x_22;
x_13 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_size(x_13);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(x_1, x_5, x_13, x_15, x_13, x_16, x_17, x_18, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_addSimpTheorem___spec__2(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_addSimpTheorem(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__14;
x_4 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__17;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__16;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__19;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__13;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__11;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__21;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__9;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__23;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__24;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__7;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__25;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__26;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__5;
x_3 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__27;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__28;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_addSimpTheoremEntry(x_1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(x_1, x_7, x_8);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_mkSimpExt___closed__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1;
x_3 = l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_instInhabitedExtensionState___spec__1;
x_4 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpExt___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Meta_mkSimpExt___closed__3;
x_4 = l_Lean_Meta_mkSimpExt___closed__2;
x_5 = l_Lean_Meta_mkSimpExt___closed__4;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
x_7 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_6, x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__3;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Meta_getSimpExtension_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtensionMapRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_getSimpExtension_x3f___closed__1;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_1);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_7, x_20);
lean_dec(x_7);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(x_1, x_21);
lean_dec(x_21);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = l_Lean_Name_hash___override(x_1);
x_28 = 32;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = 16;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = 1;
x_37 = lean_usize_sub(x_35, x_36);
x_38 = lean_usize_land(x_34, x_37);
x_39 = lean_array_uget(x_25, x_38);
lean_dec(x_25);
x_40 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(x_1, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_24);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_getSimpExtension_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getSimpExtension_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_addSimpTheoremEntry(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_4);
x_14 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_12, x_13);
lean_dec(x_13);
lean_ctor_set(x_1, 4, x_14);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_17, x_22, x_23, x_1);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_array_get_size(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_25, x_33, x_34, x_1);
lean_dec(x_25);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_ctor_get(x_1, 4);
x_46 = lean_ctor_get(x_1, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_47, sizeof(void*)*1 + 1, x_4);
x_48 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_SimpTheorems_eraseCore___spec__1(x_45, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_46);
x_50 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
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
x_54 = lean_array_get_size(x_51);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_lt(x_55, x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_54, x_54);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_62 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_51, x_60, x_61, x_49);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_53;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_49);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_66 = x_50;
} else {
 lean_dec_ref(x_50);
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
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constant expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SimpTheorem_getValue___closed__1;
x_2 = l_Lean_Meta_SimpTheorem_getValue___closed__2;
x_3 = lean_unsigned_to_nat(1757u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_SimpTheorem_getValue___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_Lean_Expr_isConst(x_7);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_size(x_9);
x_11 = 0;
lean_inc(x_9);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_9, x_14);
lean_dec(x_7);
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
x_18 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_9, x_16);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Array_isEmpty___rarg(x_20);
if (x_21 == 0)
{
size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_array_size(x_20);
x_23 = 0;
lean_inc(x_20);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(x_22, x_23, x_20, x_2, x_3, x_4, x_5, x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_20, x_26);
lean_dec(x_7);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_20, x_28);
lean_dec(x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_32 = l_Lean_Expr_constName_x21(x_7);
x_33 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_32, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Lean_ConstantInfo_levelParams(x_35);
lean_dec(x_35);
x_38 = l_List_isEmpty___rarg(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_33);
x_39 = lean_box(0);
x_40 = l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_37, x_39, x_2, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_7) == 4)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = l_ptrEqList___rarg(x_44, x_42);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_7);
x_46 = l_Lean_Expr_const___override(x_43, x_42);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
lean_dec(x_43);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_7);
return x_40;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = lean_ctor_get(x_7, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
x_51 = l_ptrEqList___rarg(x_50, x_47);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
x_52 = l_Lean_Expr_const___override(x_49, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_47);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_7);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_40, 0);
lean_dec(x_56);
x_57 = l_Lean_Meta_SimpTheorem_getValue___closed__4;
x_58 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_57);
lean_ctor_set(x_40, 0, x_58);
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_dec(x_40);
x_60 = l_Lean_Meta_SimpTheorem_getValue___closed__4;
x_61 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_dec(x_37);
lean_ctor_set(x_33, 0, x_7);
return x_33;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_33, 0);
x_64 = lean_ctor_get(x_33, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_33);
x_65 = l_Lean_ConstantInfo_levelParams(x_63);
lean_dec(x_63);
x_66 = l_List_isEmpty___rarg(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(0);
x_68 = l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_65, x_67, x_2, x_3, x_4, x_5, x_64);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_7, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_7, 1);
lean_inc(x_73);
x_74 = l_ptrEqList___rarg(x_73, x_69);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_7);
x_75 = l_Lean_Expr_const___override(x_72, x_69);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
return x_76;
}
else
{
lean_object* x_77; 
lean_dec(x_72);
lean_dec(x_69);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_7);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_7);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_79 = x_68;
} else {
 lean_dec_ref(x_68);
 x_79 = lean_box(0);
}
x_80 = l_Lean_Meta_SimpTheorem_getValue___closed__4;
x_81 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_65);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_7);
lean_ctor_set(x_83, 1, x_64);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_7);
x_84 = !lean_is_exclusive(x_33);
if (x_84 == 0)
{
return x_33;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_33, 0);
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_33);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_13, x_1, x_9, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_mk(x_16);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(x_18, x_19, x_17);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_array_mk(x_21);
x_24 = lean_array_size(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(x_24, x_25, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_7, x_6, x_16);
x_18 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_1);
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_15, x_2, x_15, x_3, x_4, x_18, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_6, x_22);
x_24 = lean_array_uset(x_17, x_6, x_20);
x_6 = x_23;
x_7 = x_24;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
uint64_t x_15; uint8_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_16 = 2;
lean_ctor_set_uint8(x_13, 9, x_16);
x_17 = 2;
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_shift_left(x_18, x_17);
x_20 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1;
x_21 = lean_uint64_lor(x_19, x_20);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_size(x_23);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1(x_1, x_2, x_4, x_6, x_25, x_26, x_23, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint64_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; 
x_40 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_41 = lean_ctor_get_uint8(x_13, 0);
x_42 = lean_ctor_get_uint8(x_13, 1);
x_43 = lean_ctor_get_uint8(x_13, 2);
x_44 = lean_ctor_get_uint8(x_13, 3);
x_45 = lean_ctor_get_uint8(x_13, 4);
x_46 = lean_ctor_get_uint8(x_13, 5);
x_47 = lean_ctor_get_uint8(x_13, 6);
x_48 = lean_ctor_get_uint8(x_13, 7);
x_49 = lean_ctor_get_uint8(x_13, 8);
x_50 = lean_ctor_get_uint8(x_13, 10);
x_51 = lean_ctor_get_uint8(x_13, 11);
x_52 = lean_ctor_get_uint8(x_13, 12);
x_53 = lean_ctor_get_uint8(x_13, 13);
x_54 = lean_ctor_get_uint8(x_13, 14);
x_55 = lean_ctor_get_uint8(x_13, 15);
x_56 = lean_ctor_get_uint8(x_13, 16);
x_57 = lean_ctor_get_uint8(x_13, 17);
lean_dec(x_13);
x_58 = 2;
x_59 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_59, 0, x_41);
lean_ctor_set_uint8(x_59, 1, x_42);
lean_ctor_set_uint8(x_59, 2, x_43);
lean_ctor_set_uint8(x_59, 3, x_44);
lean_ctor_set_uint8(x_59, 4, x_45);
lean_ctor_set_uint8(x_59, 5, x_46);
lean_ctor_set_uint8(x_59, 6, x_47);
lean_ctor_set_uint8(x_59, 7, x_48);
lean_ctor_set_uint8(x_59, 8, x_49);
lean_ctor_set_uint8(x_59, 9, x_58);
lean_ctor_set_uint8(x_59, 10, x_50);
lean_ctor_set_uint8(x_59, 11, x_51);
lean_ctor_set_uint8(x_59, 12, x_52);
lean_ctor_set_uint8(x_59, 13, x_53);
lean_ctor_set_uint8(x_59, 14, x_54);
lean_ctor_set_uint8(x_59, 15, x_55);
lean_ctor_set_uint8(x_59, 16, x_56);
lean_ctor_set_uint8(x_59, 17, x_57);
x_60 = 2;
x_61 = lean_uint64_shift_right(x_40, x_60);
x_62 = lean_uint64_shift_left(x_61, x_60);
x_63 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1;
x_64 = lean_uint64_lor(x_62, x_63);
lean_ctor_set(x_7, 0, x_59);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_64);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_array_size(x_66);
x_69 = 0;
x_70 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1(x_1, x_2, x_4, x_6, x_68, x_69, x_66, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_81 = x_65;
} else {
 lean_dec_ref(x_65);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; uint64_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; 
x_83 = lean_ctor_get(x_7, 0);
x_84 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_85 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_86 = lean_ctor_get(x_7, 1);
x_87 = lean_ctor_get(x_7, 2);
x_88 = lean_ctor_get(x_7, 3);
x_89 = lean_ctor_get(x_7, 4);
x_90 = lean_ctor_get(x_7, 5);
x_91 = lean_ctor_get(x_7, 6);
x_92 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_93 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_83);
lean_dec(x_7);
x_94 = lean_ctor_get_uint8(x_83, 0);
x_95 = lean_ctor_get_uint8(x_83, 1);
x_96 = lean_ctor_get_uint8(x_83, 2);
x_97 = lean_ctor_get_uint8(x_83, 3);
x_98 = lean_ctor_get_uint8(x_83, 4);
x_99 = lean_ctor_get_uint8(x_83, 5);
x_100 = lean_ctor_get_uint8(x_83, 6);
x_101 = lean_ctor_get_uint8(x_83, 7);
x_102 = lean_ctor_get_uint8(x_83, 8);
x_103 = lean_ctor_get_uint8(x_83, 10);
x_104 = lean_ctor_get_uint8(x_83, 11);
x_105 = lean_ctor_get_uint8(x_83, 12);
x_106 = lean_ctor_get_uint8(x_83, 13);
x_107 = lean_ctor_get_uint8(x_83, 14);
x_108 = lean_ctor_get_uint8(x_83, 15);
x_109 = lean_ctor_get_uint8(x_83, 16);
x_110 = lean_ctor_get_uint8(x_83, 17);
if (lean_is_exclusive(x_83)) {
 x_111 = x_83;
} else {
 lean_dec_ref(x_83);
 x_111 = lean_box(0);
}
x_112 = 2;
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 0, 18);
} else {
 x_113 = x_111;
}
lean_ctor_set_uint8(x_113, 0, x_94);
lean_ctor_set_uint8(x_113, 1, x_95);
lean_ctor_set_uint8(x_113, 2, x_96);
lean_ctor_set_uint8(x_113, 3, x_97);
lean_ctor_set_uint8(x_113, 4, x_98);
lean_ctor_set_uint8(x_113, 5, x_99);
lean_ctor_set_uint8(x_113, 6, x_100);
lean_ctor_set_uint8(x_113, 7, x_101);
lean_ctor_set_uint8(x_113, 8, x_102);
lean_ctor_set_uint8(x_113, 9, x_112);
lean_ctor_set_uint8(x_113, 10, x_103);
lean_ctor_set_uint8(x_113, 11, x_104);
lean_ctor_set_uint8(x_113, 12, x_105);
lean_ctor_set_uint8(x_113, 13, x_106);
lean_ctor_set_uint8(x_113, 14, x_107);
lean_ctor_set_uint8(x_113, 15, x_108);
lean_ctor_set_uint8(x_113, 16, x_109);
lean_ctor_set_uint8(x_113, 17, x_110);
x_114 = 2;
x_115 = lean_uint64_shift_right(x_84, x_114);
x_116 = lean_uint64_shift_left(x_115, x_114);
x_117 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1;
x_118 = lean_uint64_lor(x_116, x_117);
x_119 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_86);
lean_ctor_set(x_119, 2, x_87);
lean_ctor_set(x_119, 3, x_88);
lean_ctor_set(x_119, 4, x_89);
lean_ctor_set(x_119, 5, x_90);
lean_ctor_set(x_119, 6, x_91);
lean_ctor_set_uint64(x_119, sizeof(void*)*7, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*7 + 8, x_85);
lean_ctor_set_uint8(x_119, sizeof(void*)*7 + 9, x_92);
lean_ctor_set_uint8(x_119, sizeof(void*)*7 + 10, x_93);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_119);
x_120 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_5, x_119, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_array_size(x_121);
x_124 = 0;
x_125 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1(x_1, x_2, x_4, x_6, x_123, x_124, x_121, x_119, x_8, x_9, x_10, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_132 = x_125;
} else {
 lean_dec_ref(x_125);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_119);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_120, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_136 = x_120;
} else {
 lean_dec_ref(x_120);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___spec__1(x_1, x_2, x_13, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_instInhabitedProjectionFunctionInfo;
x_10 = l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1;
x_11 = l_Lean_MapDeclarationExtension_contains___rarg(x_9, x_10, x_8, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instInhabitedProjectionFunctionInfo;
x_17 = l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1;
x_18 = l_Lean_MapDeclarationExtension_contains___rarg(x_16, x_17, x_15, x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_5 = l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_isReducible___at___private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault___spec__3(x_1, x_2, x_3, x_7);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_ignoreEquations(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Meta_isRecursiveDefinition(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 1;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___closed__1;
x_19 = lean_box(0);
x_20 = lean_apply_4(x_18, x_19, x_3, x_4, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_Meta_hasSmartUnfoldingDecl(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2(x_1, x_11, x_2, x_3, x_8);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_Meta_hasSmartUnfoldingDecl(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2(x_1, x_19, x_2, x_3, x_16);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_nat_dec_lt(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_array_fget(x_1, x_5);
x_24 = lean_unsigned_to_nat(100u);
x_25 = lean_nat_dec_lt(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_nat_sub(x_24, x_5);
x_27 = 1;
x_28 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_Lean_Meta_SimpTheorems_addConst(x_4, x_23, x_27, x_28, x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
x_16 = x_32;
x_17 = x_31;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
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
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_5, x_37);
x_39 = lean_nat_dec_eq(x_38, x_2);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_40 = 1;
x_41 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_Meta_SimpTheorems_addConst(x_4, x_23, x_40, x_41, x_37, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_16 = x_45;
x_17 = x_44;
goto block_22;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 1;
x_51 = 0;
x_52 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_53 = l_Lean_Meta_SimpTheorems_addConst(x_4, x_23, x_50, x_51, x_52, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_16 = x_56;
x_17 = x_55;
goto block_22;
}
else
{
uint8_t x_57; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_20;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_addDeclToUnfold___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_8 = l_Lean_Meta_SimpTheorems_ignoreEquations(x_2, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Meta_getEqnsFor_x3f(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(x_21, x_22, x_25, x_1, x_23, lean_box(0), lean_box(0), x_3, x_4, x_5, x_6, x_20);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_29 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(x_2, x_5, x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_SimpTheorems_addDeclToUnfold___closed__1;
x_33 = lean_unbox(x_30);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_apply_7(x_32, x_27, x_34, x_3, x_4, x_5, x_6, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_27, x_2);
x_37 = lean_box(0);
x_38 = lean_apply_7(x_32, x_36, x_37, x_3, x_4, x_5, x_6, x_31);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_26);
if (x_43 == 0)
{
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
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
uint8_t x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_12);
if (x_47 == 0)
{
return x_12;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_12);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_8);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_8, 0);
lean_dec(x_52);
x_53 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
lean_ctor_set(x_8, 0, x_53);
return x_8;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_dec(x_8);
x_55 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_SimpTheorems_addDeclToUnfold___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_addDeclToUnfold___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isConst(x_4);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
lean_inc(x_16);
lean_ctor_set(x_9, 0, x_16);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_17);
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(x_2, x_3, x_4, x_6, x_5, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_21, x_26, x_27, x_1);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_array_get_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_29, x_37, x_38, x_1);
lean_dec(x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; uint64_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_47 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_48 = lean_ctor_get(x_9, 1);
x_49 = lean_ctor_get(x_9, 2);
x_50 = lean_ctor_get(x_9, 3);
x_51 = lean_ctor_get(x_9, 4);
x_52 = lean_ctor_get(x_9, 5);
x_53 = lean_ctor_get(x_9, 6);
x_54 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_55 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
lean_inc(x_45);
x_56 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_51);
lean_ctor_set(x_56, 5, x_52);
lean_ctor_set(x_56, 6, x_53);
lean_ctor_set_uint64(x_56, sizeof(void*)*7, x_46);
lean_ctor_set_uint8(x_56, sizeof(void*)*7 + 8, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*7 + 9, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*7 + 10, x_55);
x_57 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(x_2, x_3, x_4, x_6, x_5, x_7, x_56, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
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
x_61 = lean_array_get_size(x_58);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_58);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_61, x_61);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_58);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpTheorems_addConst___spec__1(x_58, x_67, x_68, x_1);
lean_dec(x_58);
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_59);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_73 = x_57;
} else {
 lean_dec_ref(x_57);
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
lean_object* x_75; lean_object* x_76; 
lean_dec(x_3);
lean_dec(x_2);
x_75 = l_Lean_Expr_constName_x21(x_4);
lean_dec(x_4);
x_76 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_75, x_6, x_5, x_7, x_9, x_10, x_11, x_12, x_13);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Meta_SimpTheorems_add(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_fget(x_1, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_1, x_12, x_16);
x_18 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_19 = 0;
x_20 = 1;
x_21 = lean_unsigned_to_nat(1000u);
x_22 = l_Lean_Meta_SimpTheorems_add(x_15, x_2, x_18, x_3, x_19, x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_array_fset(x_17, x_12, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_array_fset(x_17, x_12, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_17);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = l_Lean_Meta_mkSimpExt___closed__2;
x_36 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1;
x_37 = 0;
x_38 = 1;
x_39 = lean_unsigned_to_nat(1000u);
x_40 = l_Lean_Meta_SimpTheorems_add(x_35, x_2, x_36, x_3, x_37, x_38, x_39, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
x_44 = lean_array_mk(x_43);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_34);
x_48 = lean_array_mk(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpTheoremsArray_eraseTheorem___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists___spec__1(x_7, x_1);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isErased___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isErased(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_6, x_1);
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
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(x_6, x_1);
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
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___spec__1(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedOrigin___closed__1 = _init_l_Lean_Meta_instInhabitedOrigin___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedOrigin___closed__1);
l_Lean_Meta_instInhabitedOrigin = _init_l_Lean_Meta_instInhabitedOrigin();
lean_mark_persistent(l_Lean_Meta_instInhabitedOrigin);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__8);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__9);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__10);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__11);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__12);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__13);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__14);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__15);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__16 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__16);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__17 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__17);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__18 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____closed__18);
l_Lean_Meta_instReprOrigin___closed__1 = _init_l_Lean_Meta_instReprOrigin___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprOrigin___closed__1);
l_Lean_Meta_instReprOrigin = _init_l_Lean_Meta_instReprOrigin();
lean_mark_persistent(l_Lean_Meta_instReprOrigin);
l_Lean_Meta_instLTOrigin = _init_l_Lean_Meta_instLTOrigin();
lean_mark_persistent(l_Lean_Meta_instLTOrigin);
l_Lean_Meta_instInhabitedSimpTheorem___closed__1 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__1);
l_Lean_Meta_instInhabitedSimpTheorem___closed__2 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__2);
l_Lean_Meta_instInhabitedSimpTheorem___closed__3 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__3);
l_Lean_Meta_instInhabitedSimpTheorem___closed__4 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__4);
l_Lean_Meta_instInhabitedSimpTheorem___closed__5 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__5();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__5);
l_Lean_Meta_instInhabitedSimpTheorem = _init_l_Lean_Meta_instInhabitedSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem);
l_Lean_Meta_isRflProofCore___closed__1 = _init_l_Lean_Meta_isRflProofCore___closed__1();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__1);
l_Lean_Meta_isRflProofCore___closed__2 = _init_l_Lean_Meta_isRflProofCore___closed__2();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__2);
l_Lean_Meta_isRflProofCore___closed__3 = _init_l_Lean_Meta_isRflProofCore___closed__3();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__3);
l_Lean_Meta_isRflProofCore___closed__4 = _init_l_Lean_Meta_isRflProofCore___closed__4();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__4);
l_Lean_Meta_isRflProofCore___closed__5 = _init_l_Lean_Meta_isRflProofCore___closed__5();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__5);
l_Lean_Meta_isRflProofCore___closed__6 = _init_l_Lean_Meta_isRflProofCore___closed__6();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__6);
l_Lean_Meta_isRflProofCore___closed__7 = _init_l_Lean_Meta_isRflProofCore___closed__7();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__7);
l_Lean_Meta_isRflProofCore___closed__8 = _init_l_Lean_Meta_isRflProofCore___closed__8();
lean_mark_persistent(l_Lean_Meta_isRflProofCore___closed__8);
l_Lean_Meta_instToFormatSimpTheorem___closed__1 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__1);
l_Lean_Meta_instToFormatSimpTheorem___closed__2 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__2);
l_Lean_Meta_instToFormatSimpTheorem___closed__3 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__3);
l_Lean_Meta_instToFormatSimpTheorem___closed__4 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__4);
l_Lean_Meta_instToFormatSimpTheorem___closed__5 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__5();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__5);
l_Lean_Meta_instToFormatSimpTheorem___closed__6 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__6();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__6);
l_Lean_Meta_instToFormatSimpTheorem___closed__7 = _init_l_Lean_Meta_instToFormatSimpTheorem___closed__7();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___closed__7);
l_Lean_Meta_ppOrigin___rarg___closed__1 = _init_l_Lean_Meta_ppOrigin___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__1);
l_Lean_Meta_ppOrigin___rarg___closed__2 = _init_l_Lean_Meta_ppOrigin___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__2);
l_Lean_Meta_ppOrigin___rarg___closed__3 = _init_l_Lean_Meta_ppOrigin___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__3);
l_Lean_Meta_ppOrigin___rarg___closed__4 = _init_l_Lean_Meta_ppOrigin___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__4);
l_Lean_Meta_ppOrigin___rarg___closed__5 = _init_l_Lean_Meta_ppOrigin___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__5);
l_Lean_Meta_ppOrigin___rarg___closed__6 = _init_l_Lean_Meta_ppOrigin___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__6);
l_Lean_Meta_ppOrigin___rarg___closed__7 = _init_l_Lean_Meta_ppOrigin___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_ppOrigin___rarg___closed__7);
l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__1);
l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___rarg___lambda__1___closed__2);
l_Lean_Meta_ppSimpTheorem___rarg___lambda__2___closed__1 = _init_l_Lean_Meta_ppSimpTheorem___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___rarg___lambda__2___closed__1);
l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__1 = _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__1);
l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2 = _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1___closed__2);
l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1 = _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1);
l_Lean_Meta_instInhabitedSimpTheorems = _init_l_Lean_Meta_instInhabitedSimpTheorems();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems);
l_Lean_Meta_simpGlobalConfig___closed__1 = _init_l_Lean_Meta_simpGlobalConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig___closed__1);
l_Lean_Meta_simpGlobalConfig___closed__2 = _init_l_Lean_Meta_simpGlobalConfig___closed__2();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig___closed__2);
l_Lean_Meta_simpGlobalConfig = _init_l_Lean_Meta_simpGlobalConfig();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig);
l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__1();
l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_SimpTheorems_eraseCore___spec__5___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpTheoremEntry___spec__9___closed__2);
l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13___closed__1 = _init_l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_addSimpTheoremEntry___spec__13___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpTheoremEntry___spec__1___closed__4);
l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__1 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__1);
l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__2 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__2);
l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__3 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__3);
l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__4 = _init_l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___rarg___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__8);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lambda__3___closed__9);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__2);
l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___spec__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__8);
l_Lean_Meta_instInhabitedSimpEntry___closed__1 = _init_l_Lean_Meta_instInhabitedSimpEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry___closed__1);
l_Lean_Meta_instInhabitedSimpEntry = _init_l_Lean_Meta_instInhabitedSimpEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__1);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1___closed__2);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__1);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__2);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__3);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__4 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__4);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__5 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__5);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__6 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__6);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__7 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__7);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__8 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__8);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__9 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__9);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__10);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__11 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__11);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__12 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__12);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__13 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__13);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__14 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__14);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__15 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__15);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__16 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__16);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__17 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__17);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__18 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__18);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__19 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__19);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__20 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__20);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__21 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__21);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__22 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__22);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__23 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__23);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__24 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__24);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__25 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__25);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__26 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__26();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__26);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__27 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__27();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__27);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__28 = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__28();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505____closed__28);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5505_);
l_Lean_Meta_mkSimpExt___closed__1 = _init_l_Lean_Meta_mkSimpExt___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__1);
l_Lean_Meta_mkSimpExt___closed__2 = _init_l_Lean_Meta_mkSimpExt___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__2);
l_Lean_Meta_mkSimpExt___closed__3 = _init_l_Lean_Meta_mkSimpExt___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__3);
l_Lean_Meta_mkSimpExt___closed__4 = _init_l_Lean_Meta_mkSimpExt___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563____closed__3);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5563_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtensionMapRef);
lean_dec_ref(res);
}l_Lean_Meta_getSimpExtension_x3f___closed__1 = _init_l_Lean_Meta_getSimpExtension_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_getSimpExtension_x3f___closed__1);
l_Lean_Meta_SimpTheorem_getValue___closed__1 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__1);
l_Lean_Meta_SimpTheorem_getValue___closed__2 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__2);
l_Lean_Meta_SimpTheorem_getValue___closed__3 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__3);
l_Lean_Meta_SimpTheorem_getValue___closed__4 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___closed__1();
l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1 = _init_l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1();
lean_mark_persistent(l_Lean_isProjectionFn___at_Lean_Meta_SimpTheorems_ignoreEquations___spec__1___closed__1);
l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___closed__1 = _init_l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___lambda__2___closed__1);
l_Lean_Meta_SimpTheorems_addDeclToUnfold___closed__1 = _init_l_Lean_Meta_SimpTheorems_addDeclToUnfold___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_addDeclToUnfold___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
