// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpTheorems
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.DiscrTree Lean.Meta.AppBuilder Lean.Meta.Eqns Lean.Meta.Tactic.AuxLemma Lean.DefEqAttrib Lean.DocString
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
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l___auto___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__0;
static lean_object* l_Lean_Meta_mkSimpTheoremFromConst___closed__1;
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addSimpEntry(lean_object*, lean_object*);
lean_object* l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__0;
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__2;
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
static lean_object* l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpEntry;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__3;
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l___auto___closed__19____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableOrigin___lam__0(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2031_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromConst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11;
static lean_object* l___auto___closed__22____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedOrigin___closed__0;
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableLtOrigin___boxed(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__0;
static lean_object* l___auto___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
static lean_object* l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0___closed__0;
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__7;
lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__0;
static lean_object* l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__19;
static lean_object* l___auto___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableLtOrigin(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__1;
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_beqConstantKind____x40_Lean_Environment___hyg_1543_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorem;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem;
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpGlobalConfig___closed__0;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin;
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_logWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l___auto___closed__27____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__1;
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__6;
static lean_object* l___auto___closed__20____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromExpr(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOrigin___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_ignoreEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addSimpTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpEntryOfDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addSimpTheorem___closed__3;
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__5;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLetDeclToUnfold___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1___boxed(lean_object*);
static lean_object* l_Lean_Meta_addSimpTheorem___closed__0;
static lean_object* l_Lean_Meta_instInhabitedSimpEntry___closed__0;
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_dsimp_useDefEqAttr;
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__0(lean_object*, lean_object*);
static lean_object* l___auto___closed__17____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_debug_tactic_simp_checkDefEqAttr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__25____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___boxed(lean_object**);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addSimpTheorem_updateLemmaNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpGlobalConfig___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26;
static lean_object* l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27;
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__0;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l___auto___closed__24____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__7;
static lean_object* l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20;
static lean_object* l___auto___closed__26____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__4;
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1(lean_object*);
static lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__0;
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addSimpTheorem___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1;
static uint64_t l_Lean_Meta_mkSimpTheoremFromExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__8;
lean_object* l_Array_insertIdx_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_ignoreEquations(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__0;
lean_object* l_Lean_isReducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addSimpTheorem___closed__4;
static lean_object* l_Lean_Meta_reprOrigin___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__1;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3;
static lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__2;
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4;
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l___auto___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__2;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpGlobalConfig;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_instLTOrigin;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__3;
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__5;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__0;
static lean_object* l_Lean_Meta_reprOrigin___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpExt___closed__2;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__2;
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_defeqAttr;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3;
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
static lean_object* l_Lean_Meta_instReprOrigin___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unerase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__14____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__0;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___auto___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT uint8_t l_Lean_Meta_instToFormatSimpTheorem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__0;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__9;
static lean_object* l___auto___closed__23____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__17;
static lean_object* l_Lean_Meta_ppOrigin___redArg___closed__4;
static lean_object* l___auto___closed__16____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
static lean_object* l___auto___closed__18____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_converse(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_addSimpTheorem___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Origin_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOrigin;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l_Lean_Meta_addSimpTheorem___closed__6;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtensionMapRef;
static lean_object* l_Lean_Meta_addSimpTheorem___closed__5;
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__14;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__21;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__13;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__5;
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___redArg___lam__0___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSimpTheoremFromConst___closed__0;
static lean_object* l_Lean_Meta_addSimpTheorem___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0;
static lean_object* l_Lean_Meta_reprOrigin___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_uneraseSimpEntry(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getSimpExtension_x3f___closed__0;
lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
static lean_object* l_Lean_Meta_instInhabitedSimpTheorems___closed__1;
static lean_object* l_Lean_Meta_reprOrigin___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorem_getValue___closed__0;
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Lean_Meta_reprOrigin___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__0;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__28;
lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___auto___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8;
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprOrigin;
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backward", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("useDefEqAttr", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Use `defeq` attribute rather than checking theorem body to decide whether a theroem can be used in `dsimp` or with `implicitDefEqProofs`.", 137, 137);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_4 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_5 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_3 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_4 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkDefEqAttr", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_3 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_4 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("If true, whenever `dsimp` fails to apply a rewrite rule because it is not marked as `defeq`, check whether it would have been considered as a rfl theorem before the introduction of the `defeq` attribute, and warn if it was. Note that this is a costly check.", 257, 257);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_3 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_4 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_5 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_6 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_7 = l_Lean_Name_mkStr6(x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_3 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOrigin___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_5);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOrigin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedOrigin___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.decl", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reprOrigin___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_reprOrigin___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.fvar", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reprOrigin___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_reprOrigin___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.stx", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reprOrigin___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_reprOrigin___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Origin.other", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reprOrigin___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reprOrigin___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_reprOrigin___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_24; uint8_t x_25; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_6 = x_26;
goto block_23;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_6 = x_27;
goto block_23;
}
block_23:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_7 = lean_box(1);
x_8 = l_Lean_Meta_reprOrigin___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_9 = lean_unsigned_to_nat(1024u);
x_10 = l_Lean_Name_reprPrec(x_3, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Bool_repr___redArg(x_4);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = l_Bool_repr___redArg(x_5);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = l_Repr_addAppParen(x_20, x_2);
return x_22;
}
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(1024u);
x_41 = lean_nat_dec_le(x_40, x_2);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_29 = x_42;
goto block_39;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_29 = x_43;
goto block_39;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_30 = l_Lean_Meta_reprOrigin___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_31 = lean_unsigned_to_nat(1024u);
x_32 = l_Lean_Name_reprPrec(x_28, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = l_Repr_addAppParen(x_36, x_2);
return x_38;
}
}
case 2:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_62; uint8_t x_63; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_46 = x_1;
} else {
 lean_dec_ref(x_1);
 x_46 = lean_box(0);
}
x_62 = lean_unsigned_to_nat(1024u);
x_63 = lean_nat_dec_le(x_62, x_2);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_47 = x_64;
goto block_61;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_47 = x_65;
goto block_61;
}
block_61:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_48 = lean_box(1);
x_49 = l_Lean_Meta_reprOrigin___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_50 = lean_unsigned_to_nat(1024u);
x_51 = l_Lean_Name_reprPrec(x_44, x_50);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(5, 2, 0);
} else {
 x_52 = x_46;
 lean_ctor_set_tag(x_52, 5);
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
x_54 = l_Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2031_(x_45, x_50);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_59);
x_60 = l_Repr_addAppParen(x_58, x_2);
return x_60;
}
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_78; uint8_t x_79; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_78 = lean_unsigned_to_nat(1024u);
x_79 = lean_nat_dec_le(x_78, x_2);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_67 = x_80;
goto block_77;
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_67 = x_81;
goto block_77;
}
block_77:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_68 = l_Lean_Meta_reprOrigin___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_;
x_69 = lean_unsigned_to_nat(1024u);
x_70 = l_Lean_Name_reprPrec(x_66, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_unbox(x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_75);
x_76 = l_Repr_addAppParen(x_74, x_2);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprOrigin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprOrigin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprOrigin___closed__0;
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
lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
if (x_4 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_6 = x_13;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
if (lean_is_scalar(x_5)) {
 x_7 = lean_alloc_ctor(0, 1, 2);
} else {
 x_7 = x_5;
}
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOrigin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_11 = lean_name_eq(x_7, x_9);
if (x_11 == 0)
{
return x_11;
}
else
{
if (x_8 == 0)
{
if (x_10 == 0)
{
return x_11;
}
else
{
return x_8;
}
}
else
{
return x_10;
}
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
x_3 = x_16;
goto block_6;
}
}
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Meta_instBEqOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqOrigin___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableOrigin___lam__0(lean_object* x_1) {
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
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Lean_Name_hash___override(x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_instHashableOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instHashableOrigin___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Origin_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_11 = l_Lean_Name_lt(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_name_eq(x_7, x_9);
if (x_12 == 0)
{
if (x_12 == 0)
{
return x_12;
}
else
{
return x_10;
}
}
else
{
if (x_8 == 0)
{
if (x_12 == 0)
{
return x_12;
}
else
{
return x_10;
}
}
else
{
if (x_11 == 0)
{
return x_11;
}
else
{
return x_10;
}
}
}
}
else
{
return x_11;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
x_3 = x_17;
goto block_6;
}
}
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_lt(x_3, x_4);
return x_5;
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
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedSimpTheorem___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_1 = l_Lean_Meta_instInhabitedOrigin___closed__0;
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Meta_instInhabitedSimpTheorem___closed__3;
x_5 = l_Lean_Meta_instInhabitedSimpTheorem___closed__0;
x_6 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_1);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*5 + 1, x_8);
x_9 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*5 + 2, x_9);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__4;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symm", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_1, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__3;
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Expr_isAppOfArity(x_2, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__5;
x_20 = l_Lean_Expr_isAppOfArity(x_2, x_19, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__7;
x_22 = lean_unsigned_to_nat(4u);
x_23 = l_Lean_Expr_isAppOfArity(x_2, x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_25 = l_Lean_Expr_isConst(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Expr_constName_x21(x_24);
lean_dec(x_24);
x_29 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(x_28, x_3, x_4, x_5);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_2 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(x_13);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_box(x_13);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Environment_findAsync_x3f(x_10, x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_6);
x_12 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1;
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = l_Lean_MessageData_ofExpr(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_18, x_3, x_4, x_9);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_1);
x_24 = l_Lean_Environment_findAsync_x3f(x_23, x_1, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1;
x_26 = lean_box(0);
x_27 = l_Lean_Expr_const___override(x_1, x_26);
x_28 = l_Lean_MessageData_ofExpr(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_31, x_3, x_4, x_22);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
return x_34;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_backward_dsimp_useDefEqAttr;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isRflTheorem theorem body", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_defeqAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__0;
x_7 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(x_1, x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_11 = lean_box(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_traceBlock___redArg(x_14, x_13, x_2, x_3, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(x_21, x_20, x_2, x_3, x_19);
lean_dec(x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_25 = lean_box(x_7);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_box(x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_8, 0);
lean_dec(x_34);
x_35 = lean_box(x_7);
lean_ctor_set(x_8, 0, x_35);
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_box(x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_2);
x_43 = lean_st_ref_get(x_3, x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2;
x_48 = l_Lean_TagAttribute_hasTag(x_47, x_46, x_1);
x_49 = lean_box(x_48);
lean_ctor_set(x_43, 0, x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2;
x_54 = l_Lean_TagAttribute_hasTag(x_53, x_52, x_1);
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_withoutExporting___at___Lean_compileDecls_doCompile_spec__8___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(x_7, x_4, x_5, x_6);
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
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(x_10, x_1, x_4, x_5, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_isRflProof___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instToFormatSimpTheorem___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":perm", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_22 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
lean_dec(x_2);
if (x_21 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_23 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3;
x_23 = x_27;
goto block_25;
}
block_19:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Name_toString(x_5, x_7, x_1);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__1;
x_11 = l_Nat_reprFast(x_3);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__2;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_4);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
block_25:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_3 = x_20;
x_4 = x_23;
x_5 = x_24;
goto block_19;
}
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instToFormatSimpTheorem___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instToFormatSimpTheorem___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instToFormatSimpTheorem___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("↓ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("↓ ← ", 8, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___redArg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___redArg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_MessageData_ofConstName(x_7, x_11);
if (x_8 == 0)
{
if (x_9 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Meta_ppOrigin___redArg___closed__1;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_13);
x_14 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_apply_2(x_6, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Meta_ppOrigin___redArg___closed__4;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_17);
x_18 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_apply_2(x_6, lean_box(0), x_19);
return x_20;
}
}
else
{
if (x_9 == 0)
{
lean_object* x_21; 
lean_free_object(x_1);
x_21 = lean_apply_2(x_6, lean_box(0), x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Meta_ppOrigin___redArg___closed__6;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_22);
x_23 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_apply_2(x_6, lean_box(0), x_24);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_1);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Expr_fvar___override(x_27);
x_29 = l_Lean_MessageData_ofExpr(x_28);
x_30 = lean_apply_2(x_26, lean_box(0), x_29);
return x_30;
}
case 2:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_1);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_dec(x_4);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_MessageData_ofSyntax(x_32);
x_34 = lean_apply_2(x_31, lean_box(0), x_33);
return x_34;
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_1);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = l_Lean_MessageData_ofName(x_36);
x_38 = lean_apply_2(x_35, lean_box(0), x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_MessageData_ofConstName(x_41, x_45);
if (x_42 == 0)
{
if (x_43 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = l_Lean_Meta_ppOrigin___redArg___closed__1;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_apply_2(x_40, lean_box(0), x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = l_Lean_Meta_ppOrigin___redArg___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_54 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_apply_2(x_40, lean_box(0), x_55);
return x_56;
}
}
else
{
if (x_43 == 0)
{
lean_object* x_57; 
x_57 = lean_apply_2(x_40, lean_box(0), x_46);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = l_Lean_Meta_ppOrigin___redArg___closed__6;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_46);
x_60 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_apply_2(x_40, lean_box(0), x_61);
return x_62;
}
}
}
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec(x_2);
x_65 = l_Lean_Expr_fvar___override(x_64);
x_66 = l_Lean_MessageData_ofExpr(x_65);
x_67 = lean_apply_2(x_63, lean_box(0), x_66);
return x_67;
}
case 2:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_39, 1);
lean_inc(x_68);
lean_dec(x_39);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
lean_dec(x_2);
x_70 = l_Lean_MessageData_ofSyntax(x_69);
x_71 = lean_apply_2(x_68, lean_box(0), x_70);
return x_71;
}
default: 
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_39, 1);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
lean_dec(x_2);
x_74 = l_Lean_MessageData_ofName(x_73);
x_75 = lean_apply_2(x_72, lean_box(0), x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppOrigin___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppOrigin(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_Meta_ppSimpTheorem___redArg___lam__0___closed__0;
x_6 = l_Nat_reprFast(x_1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_apply_2(x_3, lean_box(0), x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3;
x_9 = x_7;
x_10 = x_16;
goto block_14;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_ppSimpTheorem___redArg___lam__0), 4, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_8);
x_12 = l_Lean_Meta_ppOrigin___redArg(x_1, x_6);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppSimpTheorem___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppSimpTheorem(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instBEqSimpTheorem() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqSimpTheorem___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqSimpTheorem___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(2);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 18);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 17, x_24);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_simpGlobalConfig___closed__0;
x_2 = l_Lean_Meta_Config_toConfigWithKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpGlobalConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set_uint64(x_22, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 9, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 10, x_21);
x_23 = lean_apply_5(x_1, x_22, x_3, x_4, x_5, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; 
x_8 = l_Lean_Meta_simpGlobalConfig;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_10);
x_13 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
x_19 = lean_ctor_get(x_3, 5);
x_20 = lean_ctor_get(x_3, 6);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set_uint64(x_23, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 8, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 9, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 10, x_22);
x_24 = lean_apply_5(x_2, x_23, x_4, x_5, x_6, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___lam__0), 7, 1);
lean_closure_set(x_12, 0, x_4);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = lean_expr_instantiate1(x_2, x_3);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
switch (lean_obj_tag(x_1)) {
case 2:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_32; 
x_32 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_32;
}
case 10:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
x_2 = x_33;
goto _start;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_35, x_37, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_1 = x_36;
x_2 = x_38;
x_7 = x_42;
goto _start;
}
}
else
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
case 10:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_2 = x_44;
goto _start;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
lean_dec(x_2);
x_8 = x_46;
x_9 = x_47;
x_10 = x_48;
x_11 = x_49;
x_12 = x_50;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_24;
}
case 10:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_2 = x_51;
goto _start;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
lean_dec(x_2);
x_8 = x_53;
x_9 = x_54;
x_10 = x_55;
x_11 = x_56;
x_12 = x_57;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_24;
}
case 10:
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_dec(x_2);
x_2 = x_58;
goto _start;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 8:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_61);
x_67 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_61, x_64, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_62);
x_71 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_62, x_65, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1___boxed), 8, 2);
lean_closure_set(x_75, 0, x_63);
lean_closure_set(x_75, 1, x_66);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = lean_unbox(x_76);
x_79 = lean_unbox(x_77);
x_80 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(x_60, x_61, x_62, x_75, x_78, x_79, x_3, x_4, x_5, x_6, x_74);
return x_80;
}
}
else
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_71;
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
}
case 10:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_2 = x_81;
goto _start;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
case 10:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_1 = x_83;
goto _start;
}
case 11:
{
switch (lean_obj_tag(x_2)) {
case 10:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_2 = x_85;
goto _start;
}
case 11:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
lean_dec(x_2);
x_91 = lean_nat_dec_eq(x_87, x_89);
lean_dec(x_89);
lean_dec(x_87);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_7);
return x_93;
}
else
{
x_1 = x_88;
x_2 = x_90;
goto _start;
}
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_2, 1);
lean_inc(x_95);
lean_dec(x_2);
x_2 = x_95;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = x_1;
x_26 = x_2;
x_27 = x_7;
goto block_31;
}
}
}
block_24:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_9, x_11, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0___boxed), 8, 2);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_12);
x_23 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_8, x_9, x_22, x_13, x_14, x_15, x_16, x_21);
return x_23;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_18;
}
}
block_31:
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_expr_eqv(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid `simp` theorem, equation is equivalent to", 49, 49);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
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
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_16);
lean_ctor_set(x_21, 6, x_17);
lean_ctor_set_uint64(x_21, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 10, x_19);
x_22 = lean_unbox(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_DiscrTree_reduceDT(x_1, x_22, x_21, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_44; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_44 = lean_expr_eqv(x_24, x_2);
if (x_44 == 0)
{
x_27 = x_44;
goto block_43;
}
else
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isFVar(x_24);
x_27 = x_45;
goto block_43;
}
block_43:
{
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_26);
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
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1;
x_34 = l_Lean_indentExpr(x_31);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_37, x_3, x_4, x_5, x_6, x_32);
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
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_2, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Expr_appFn_x21(x_2);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_15 = l_Lean_Expr_appArg_x21(x_2);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_14, x_15, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0___boxed), 7, 0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_1, x_7, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_List_reverse___redArg(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_box(0);
x_19 = lean_box(1);
x_20 = lean_unbox(x_18);
x_21 = lean_unbox(x_18);
x_22 = lean_unbox(x_19);
lean_inc(x_1);
x_23 = l_Lean_Meta_mkLambdaFVars(x_1, x_16, x_20, x_2, x_21, x_2, x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unbox(x_18);
x_27 = lean_unbox(x_19);
lean_inc(x_1);
x_28 = l_Lean_Meta_mkForallFVars(x_1, x_17, x_26, x_2, x_2, x_27, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_24);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_30;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_free_object(x_13);
lean_free_object(x_3);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
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
lean_free_object(x_13);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_box(0);
x_44 = lean_box(1);
x_45 = lean_unbox(x_43);
x_46 = lean_unbox(x_43);
x_47 = lean_unbox(x_44);
lean_inc(x_1);
x_48 = l_Lean_Meta_mkLambdaFVars(x_1, x_41, x_45, x_2, x_46, x_2, x_47, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_43);
x_52 = lean_unbox(x_44);
lean_inc(x_1);
x_53 = l_Lean_Meta_mkForallFVars(x_1, x_42, x_51, x_2, x_2, x_52, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_56);
{
lean_object* _tmp_2 = x_40;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_55;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_49);
lean_free_object(x_3);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_1);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_42);
lean_free_object(x_3);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_1);
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_64 = x_48;
} else {
 lean_dec_ref(x_48);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
x_72 = lean_box(1);
x_73 = lean_unbox(x_71);
x_74 = lean_unbox(x_71);
x_75 = lean_unbox(x_72);
lean_inc(x_1);
x_76 = l_Lean_Meta_mkLambdaFVars(x_1, x_68, x_73, x_2, x_74, x_2, x_75, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_71);
x_80 = lean_unbox(x_72);
lean_inc(x_1);
x_81 = l_Lean_Meta_mkForallFVars(x_1, x_69, x_79, x_2, x_2, x_80, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_4);
x_3 = x_67;
x_4 = x_85;
x_9 = x_83;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_4);
lean_dec(x_1);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_4);
lean_dec(x_1);
x_91 = lean_ctor_get(x_76, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_76, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_93 = x_76;
} else {
 lean_dec_ref(x_76);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkAppN(x_1, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_3, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(x_5, x_4, x_14, x_16, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'True'", 48, 46);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__17;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__19;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_eq_false", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__21;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_eq_true", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__25;
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'False'", 49, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__28;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_44; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_44 = l_Lean_Expr_isForall(x_11);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
x_46 = lean_unsigned_to_nat(3u);
x_47 = l_Lean_Expr_isAppOfArity(x_11, x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_13);
x_48 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__4;
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Expr_isAppOfArity(x_11, x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__6;
x_52 = l_Lean_Expr_isAppOfArity(x_11, x_51, x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__8;
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Expr_isAppOfArity(x_11, x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__10;
x_57 = l_Lean_Expr_isAppOfArity(x_11, x_56, x_49);
if (x_57 == 0)
{
if (x_1 == 0)
{
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_12;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_11);
lean_dec(x_3);
x_58 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__12;
x_59 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_58, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = l_Lean_Expr_appFn_x21(x_11);
x_65 = l_Lean_Expr_appArg_x21(x_64);
lean_dec(x_64);
x_66 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_67 = l_Lean_Expr_proj___override(x_56, x_66, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_68 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_67, x_65, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_72 = l_Lean_Expr_proj___override(x_56, x_54, x_3);
x_73 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_72, x_71, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_List_appendTR___redArg(x_69, x_75);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = l_List_appendTR___redArg(x_69, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_dec(x_69);
return x_73;
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_68;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_81 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
x_112 = x_5;
x_113 = x_6;
x_114 = x_7;
x_115 = x_8;
x_116 = x_12;
goto block_179;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_81);
lean_dec(x_3);
x_180 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29;
x_181 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_180, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
return x_181;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_181);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
block_111:
{
lean_object* x_87; lean_object* x_88; 
x_87 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15;
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
x_88 = l_Lean_Meta_mkEq(x_81, x_87, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Meta_mkEqFalse(x_3, x_82, x_83, x_84, x_85, x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_91, 0, x_96);
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_89);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_89);
x_103 = !lean_is_exclusive(x_91);
if (x_103 == 0)
{
return x_91;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_91, 0);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_91);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_88);
if (x_107 == 0)
{
return x_88;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_88, 0);
x_109 = lean_ctor_get(x_88, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_88);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
block_179:
{
uint8_t x_117; 
x_117 = l_Lean_Expr_isAppOfArity(x_81, x_45, x_46);
if (x_117 == 0)
{
x_82 = x_112;
x_83 = x_113;
x_84 = x_114;
x_85 = x_115;
x_86 = x_116;
goto block_111;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = l_Lean_Expr_appFn_x21(x_81);
x_119 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_120 = l_Lean_Expr_appArg_x21(x_81);
x_121 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18;
x_122 = l_Lean_Expr_isConstOf(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20;
x_124 = l_Lean_Expr_isConstOf(x_120, x_123);
lean_dec(x_120);
if (x_124 == 0)
{
lean_dec(x_119);
x_82 = x_112;
x_83 = x_113;
x_84 = x_114;
x_85 = x_115;
x_86 = x_116;
goto block_111;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_81);
x_125 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22;
x_126 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23;
x_127 = lean_array_push(x_126, x_3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
x_128 = l_Lean_Meta_mkAppM(x_125, x_127, x_112, x_113, x_114, x_115, x_116);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24;
x_132 = l_Lean_Meta_mkEq(x_119, x_131, x_112, x_113, x_114, x_115, x_130);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_132, 0, x_137);
return x_132;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_132, 0);
x_139 = lean_ctor_get(x_132, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_132);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_129);
lean_ctor_set(x_140, 1, x_138);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_129);
x_144 = !lean_is_exclusive(x_132);
if (x_144 == 0)
{
return x_132;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_132, 0);
x_146 = lean_ctor_get(x_132, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_132);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
x_148 = !lean_is_exclusive(x_128);
if (x_148 == 0)
{
return x_128;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_128, 0);
x_150 = lean_ctor_get(x_128, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_128);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_120);
lean_dec(x_81);
x_152 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26;
x_153 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23;
x_154 = lean_array_push(x_153, x_3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
x_155 = l_Lean_Meta_mkAppM(x_152, x_154, x_112, x_113, x_114, x_115, x_116);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27;
x_159 = l_Lean_Meta_mkEq(x_119, x_158, x_112, x_113, x_114, x_115, x_157);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_159, 0, x_164);
return x_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_159, 0);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_159);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_156);
x_171 = !lean_is_exclusive(x_159);
if (x_171 == 0)
{
return x_159;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_159, 0);
x_173 = lean_ctor_get(x_159, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_159);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_119);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
x_175 = !lean_is_exclusive(x_155);
if (x_175 == 0)
{
return x_155;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_155, 0);
x_177 = lean_ctor_get(x_155, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_155);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = l_Lean_Expr_appFn_x21(x_11);
x_187 = l_Lean_Expr_appArg_x21(x_186);
lean_dec(x_186);
x_188 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
x_189 = x_5;
x_190 = x_6;
x_191 = x_7;
x_192 = x_8;
x_193 = x_12;
goto block_283;
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_3);
x_284 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29;
x_285 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_284, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_286 = !lean_is_exclusive(x_285);
if (x_286 == 0)
{
return x_285;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_285, 0);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_285);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
block_283:
{
lean_object* x_194; uint8_t x_195; 
x_194 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18;
x_195 = l_Lean_Expr_isConstOf(x_188, x_194);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20;
x_197 = l_Lean_Expr_isConstOf(x_188, x_196);
if (x_197 == 0)
{
lean_object* x_198; 
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_198 = l_Lean_Meta_mkEq(x_187, x_188, x_189, x_190, x_191, x_192, x_193);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15;
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_202 = l_Lean_Meta_mkEq(x_199, x_201, x_189, x_190, x_191, x_192, x_200);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l_Lean_Meta_mkEqFalse(x_3, x_189, x_190, x_191, x_192, x_204);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_203);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_205, 0, x_210);
return x_205;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_205, 0);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_205);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_203);
x_214 = lean_box(0);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_212);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_203);
x_217 = !lean_is_exclusive(x_205);
if (x_217 == 0)
{
return x_205;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_205, 0);
x_219 = lean_ctor_get(x_205, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_205);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_202);
if (x_221 == 0)
{
return x_202;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_202, 0);
x_223 = lean_ctor_get(x_202, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_202);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_198);
if (x_225 == 0)
{
return x_198;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_198, 0);
x_227 = lean_ctor_get(x_198, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_198);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_188);
x_229 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22;
x_230 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23;
x_231 = lean_array_push(x_230, x_3);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_232 = l_Lean_Meta_mkAppM(x_229, x_231, x_189, x_190, x_191, x_192, x_193);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24;
x_236 = l_Lean_Meta_mkEq(x_187, x_235, x_189, x_190, x_191, x_192, x_234);
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_236, 0);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_236, 0, x_241);
return x_236;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_236, 0);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_236);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_233);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_243);
return x_247;
}
}
else
{
uint8_t x_248; 
lean_dec(x_233);
x_248 = !lean_is_exclusive(x_236);
if (x_248 == 0)
{
return x_236;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_236, 0);
x_250 = lean_ctor_get(x_236, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_236);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_187);
x_252 = !lean_is_exclusive(x_232);
if (x_252 == 0)
{
return x_232;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_232, 0);
x_254 = lean_ctor_get(x_232, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_232);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_188);
x_256 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26;
x_257 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23;
x_258 = lean_array_push(x_257, x_3);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_259 = l_Lean_Meta_mkAppM(x_256, x_258, x_189, x_190, x_191, x_192, x_193);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27;
x_263 = l_Lean_Meta_mkEq(x_187, x_262, x_189, x_190, x_191, x_192, x_261);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_box(0);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_263, 0, x_268);
return x_263;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_263, 0);
x_270 = lean_ctor_get(x_263, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_263);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_270);
return x_274;
}
}
else
{
uint8_t x_275; 
lean_dec(x_260);
x_275 = !lean_is_exclusive(x_263);
if (x_275 == 0)
{
return x_263;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_263, 0);
x_277 = lean_ctor_get(x_263, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_263);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_187);
x_279 = !lean_is_exclusive(x_259);
if (x_279 == 0)
{
return x_259;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_259, 0);
x_281 = lean_ctor_get(x_259, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_259);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_290 = l_Lean_Expr_appFn_x21(x_11);
x_291 = l_Lean_Expr_appArg_x21(x_290);
lean_dec(x_290);
x_292 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_2 == 0)
{
x_293 = x_5;
x_294 = x_6;
x_295 = x_7;
x_296 = x_8;
x_297 = x_12;
goto block_351;
}
else
{
lean_object* x_352; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_292);
lean_inc(x_291);
x_352 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_291, x_292, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_293 = x_5;
x_294 = x_6;
x_295 = x_7;
x_296 = x_8;
x_297 = x_353;
goto block_351;
}
else
{
uint8_t x_354; 
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_354 = !lean_is_exclusive(x_352);
if (x_354 == 0)
{
return x_352;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_352, 0);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_352);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
block_351:
{
if (x_1 == 0)
{
lean_object* x_298; 
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
x_298 = l_Lean_Meta_mkEq(x_291, x_292, x_293, x_294, x_295, x_296, x_297);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = l_Lean_Meta_mkPropExt(x_3, x_293, x_294, x_295, x_296, x_300);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_299);
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set(x_301, 0, x_306);
return x_301;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_307 = lean_ctor_get(x_301, 0);
x_308 = lean_ctor_get(x_301, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_301);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_299);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_308);
return x_312;
}
}
else
{
uint8_t x_313; 
lean_dec(x_299);
x_313 = !lean_is_exclusive(x_301);
if (x_313 == 0)
{
return x_301;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_301, 0);
x_315 = lean_ctor_get(x_301, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_301);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
uint8_t x_317; 
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_3);
x_317 = !lean_is_exclusive(x_298);
if (x_317 == 0)
{
return x_298;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_298, 0);
x_319 = lean_ctor_get(x_298, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_298);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
}
else
{
lean_object* x_321; 
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
x_321 = l_Lean_Meta_mkEq(x_292, x_291, x_293, x_294, x_295, x_296, x_297);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
x_324 = l_Lean_Meta_mkPropExt(x_3, x_293, x_294, x_295, x_296, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = l_Lean_Meta_mkEqSymm(x_325, x_293, x_294, x_295, x_296, x_326);
if (lean_obj_tag(x_327) == 0)
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_327, 0);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_322);
x_331 = lean_box(0);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
lean_ctor_set(x_327, 0, x_332);
return x_327;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_333 = lean_ctor_get(x_327, 0);
x_334 = lean_ctor_get(x_327, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_327);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_322);
x_336 = lean_box(0);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_334);
return x_338;
}
}
else
{
uint8_t x_339; 
lean_dec(x_322);
x_339 = !lean_is_exclusive(x_327);
if (x_339 == 0)
{
return x_327;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_327, 0);
x_341 = lean_ctor_get(x_327, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_327);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_322);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
x_343 = !lean_is_exclusive(x_324);
if (x_343 == 0)
{
return x_324;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_324, 0);
x_345 = lean_ctor_get(x_324, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_324);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_3);
x_347 = !lean_is_exclusive(x_321);
if (x_347 == 0)
{
return x_321;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_321, 0);
x_349 = lean_ctor_get(x_321, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_321);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_358 = l_Lean_Expr_appFn_x21(x_11);
x_359 = l_Lean_Expr_appArg_x21(x_358);
lean_dec(x_358);
x_360 = l_Lean_Expr_appArg_x21(x_11);
if (x_2 == 0)
{
x_361 = x_5;
x_362 = x_6;
x_363 = x_7;
x_364 = x_8;
x_365 = x_12;
goto block_393;
}
else
{
lean_object* x_394; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_360);
lean_inc(x_359);
x_394 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_359, x_360, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; 
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_361 = x_5;
x_362 = x_6;
x_363 = x_7;
x_364 = x_8;
x_365 = x_395;
goto block_393;
}
else
{
uint8_t x_396; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_396 = !lean_is_exclusive(x_394);
if (x_396 == 0)
{
return x_394;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_394, 0);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_394);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
block_393:
{
if (x_1 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_3);
lean_ctor_set(x_366, 1, x_11);
x_367 = lean_box(0);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
if (lean_is_scalar(x_13)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_13;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_365);
return x_369;
}
else
{
lean_object* x_370; 
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
x_370 = l_Lean_Meta_mkEq(x_360, x_359, x_361, x_362, x_363, x_364, x_365);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_Meta_mkEqSymm(x_3, x_361, x_362, x_363, x_364, x_372);
if (lean_obj_tag(x_373) == 0)
{
uint8_t x_374; 
x_374 = !lean_is_exclusive(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_373, 0);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_371);
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set(x_373, 0, x_378);
return x_373;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_379 = lean_ctor_get(x_373, 0);
x_380 = lean_ctor_get(x_373, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_373);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_371);
x_382 = lean_box(0);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_380);
return x_384;
}
}
else
{
uint8_t x_385; 
lean_dec(x_371);
x_385 = !lean_is_exclusive(x_373);
if (x_385 == 0)
{
return x_373;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_373, 0);
x_387 = lean_ctor_get(x_373, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_373);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_364);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_3);
x_389 = !lean_is_exclusive(x_370);
if (x_389 == 0)
{
return x_370;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_370, 0);
x_391 = lean_ctor_get(x_370, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_370);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; uint8_t x_406; lean_object* x_407; 
lean_dec(x_13);
x_400 = lean_box(x_1);
x_401 = lean_box(x_2);
x_402 = lean_box(x_44);
x_403 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0___boxed), 11, 4);
lean_closure_set(x_403, 0, x_3);
lean_closure_set(x_403, 1, x_400);
lean_closure_set(x_403, 2, x_401);
lean_closure_set(x_403, 3, x_402);
x_404 = lean_box(0);
x_405 = lean_unbox(x_404);
x_406 = lean_unbox(x_404);
x_407 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_11, x_403, x_405, x_406, x_5, x_6, x_7, x_8, x_12);
return x_407;
}
block_43:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = l_Lean_Meta_mkEq(x_11, x_19, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_mkEqTrue(x_3, x_14, x_15, x_16, x_17, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_21);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_408 = !lean_is_exclusive(x_10);
if (x_408 == 0)
{
return x_10;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_10, 0);
x_410 = lean_ctor_get(x_10, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_10);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'simp', proposition expected", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__0;
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
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1;
x_12 = l_Lean_indentExpr(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_15, x_2, x_3, x_4, x_5, x_10);
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
static lean_object* _init_l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected kind of 'simp' theorem", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_forallMetaTelescopeReducing(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = l_Lean_Meta_whnfR(x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Expr_isAppOfArity(x_25, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1;
x_31 = l_Lean_indentExpr(x_25);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_31);
lean_ctor_set(x_18, 0, x_30);
x_32 = l_Lean_Meta_ppOrigin___redArg___closed__2;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_32);
lean_ctor_set(x_16, 0, x_18);
x_33 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_16, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_18);
lean_free_object(x_16);
x_38 = l_Lean_Expr_appFn_x21(x_25);
x_39 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_39);
x_40 = l_Lean_Meta_DiscrTree_mkPath(x_39, x_9, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_44 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_39, x_43, x_10, x_11, x_12, x_13, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_4);
x_47 = l_Lean_Meta_isRflProof(x_4, x_10, x_11, x_12, x_13, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 2, x_4);
lean_ctor_set(x_50, 3, x_6);
lean_ctor_set(x_50, 4, x_8);
lean_ctor_set_uint8(x_50, sizeof(void*)*5, x_7);
x_51 = lean_unbox(x_45);
lean_dec(x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*5 + 1, x_51);
x_52 = lean_unbox(x_49);
lean_dec(x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*5 + 2, x_52);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_5);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set(x_55, 3, x_6);
lean_ctor_set(x_55, 4, x_8);
lean_ctor_set_uint8(x_55, sizeof(void*)*5, x_7);
x_56 = lean_unbox(x_45);
lean_dec(x_45);
lean_ctor_set_uint8(x_55, sizeof(void*)*5 + 1, x_56);
x_57 = lean_unbox(x_53);
lean_dec(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*5 + 2, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_44);
if (x_63 == 0)
{
return x_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_40);
if (x_67 == 0)
{
return x_40;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_40, 0);
x_69 = lean_ctor_get(x_40, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_40);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_18);
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
return x_24;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_24, 0);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_24);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_76 = l_Lean_Meta_whnfR(x_75, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
x_80 = lean_unsigned_to_nat(3u);
x_81 = l_Lean_Expr_isAppOfArity(x_77, x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1;
x_83 = l_Lean_indentExpr(x_77);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Meta_ppOrigin___redArg___closed__2;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_85);
lean_ctor_set(x_16, 0, x_84);
x_86 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_16, x_10, x_11, x_12, x_13, x_78);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_16);
x_91 = l_Lean_Expr_appFn_x21(x_77);
x_92 = l_Lean_Expr_appArg_x21(x_91);
lean_dec(x_91);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_92);
x_93 = l_Lean_Meta_DiscrTree_mkPath(x_92, x_9, x_10, x_11, x_12, x_13, x_78);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Expr_appArg_x21(x_77);
lean_dec(x_77);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_97 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_92, x_96, x_10, x_11, x_12, x_13, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_4);
x_100 = l_Lean_Meta_isRflProof(x_4, x_10, x_11, x_12, x_13, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_5);
lean_ctor_set(x_104, 2, x_4);
lean_ctor_set(x_104, 3, x_6);
lean_ctor_set(x_104, 4, x_8);
lean_ctor_set_uint8(x_104, sizeof(void*)*5, x_7);
x_105 = lean_unbox(x_98);
lean_dec(x_98);
lean_ctor_set_uint8(x_104, sizeof(void*)*5 + 1, x_105);
x_106 = lean_unbox(x_101);
lean_dec(x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*5 + 2, x_106);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_98);
lean_dec(x_94);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_110 = x_100;
} else {
 lean_dec_ref(x_100);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_114 = x_97;
} else {
 lean_dec_ref(x_97);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_93, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_93, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_118 = x_93;
} else {
 lean_dec_ref(x_93);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = lean_ctor_get(x_76, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_122 = x_76;
} else {
 lean_dec_ref(x_76);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_16, 1);
lean_inc(x_124);
lean_dec(x_16);
x_125 = lean_ctor_get(x_15, 1);
lean_inc(x_125);
lean_dec(x_15);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_128 = l_Lean_Meta_whnfR(x_126, x_10, x_11, x_12, x_13, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1;
x_132 = lean_unsigned_to_nat(3u);
x_133 = l_Lean_Expr_isAppOfArity(x_129, x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_134 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1;
x_135 = l_Lean_indentExpr(x_129);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_127;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_138, x_10, x_11, x_12, x_13, x_130);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
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
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_127);
x_144 = l_Lean_Expr_appFn_x21(x_129);
x_145 = l_Lean_Expr_appArg_x21(x_144);
lean_dec(x_144);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_145);
x_146 = l_Lean_Meta_DiscrTree_mkPath(x_145, x_9, x_10, x_11, x_12, x_13, x_130);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Expr_appArg_x21(x_129);
lean_dec(x_129);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_150 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_145, x_149, x_10, x_11, x_12, x_13, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_4);
x_153 = l_Lean_Meta_isRflProof(x_4, x_10, x_11, x_12, x_13, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_5);
lean_ctor_set(x_157, 2, x_4);
lean_ctor_set(x_157, 3, x_6);
lean_ctor_set(x_157, 4, x_8);
lean_ctor_set_uint8(x_157, sizeof(void*)*5, x_7);
x_158 = lean_unbox(x_151);
lean_dec(x_151);
lean_ctor_set_uint8(x_157, sizeof(void*)*5 + 1, x_158);
x_159 = lean_unbox(x_154);
lean_dec(x_154);
lean_ctor_set_uint8(x_157, sizeof(void*)*5 + 2, x_159);
if (lean_is_scalar(x_156)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_156;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_155);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_161 = lean_ctor_get(x_153, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_153, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_163 = x_153;
} else {
 lean_dec_ref(x_153);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_147);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_165 = lean_ctor_get(x_150, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_150, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_167 = x_150;
} else {
 lean_dec_ref(x_150);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_145);
lean_dec(x_129);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_169 = lean_ctor_get(x_146, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_146, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_171 = x_146;
} else {
 lean_dec_ref(x_146);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_127);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_173 = lean_ctor_get(x_128, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_128, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_175 = x_128;
} else {
 lean_dec_ref(x_128);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = !lean_is_exclusive(x_15);
if (x_177 == 0)
{
return x_15;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_15, 0);
x_179 = lean_ctor_get(x_15, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_15);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.SimpTheorems", 34, 34);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Simp.SimpTheorems.0.Lean.Meta.mkSimpTheoremCore", 73, 73);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: origin != .fvar ⟨.anonymous⟩\n  ", 56, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(354u);
x_4 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
goto block_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_38; 
x_32 = lean_box(0);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_33 = x_38;
goto block_37;
block_37:
{
uint8_t x_34; 
x_34 = lean_name_eq(x_33, x_32);
lean_dec(x_33);
if (x_34 == 0)
{
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3;
x_36 = l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0(x_35, x_8, x_9, x_10, x_11, x_12);
return x_36;
}
}
}
block_31:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_infer_type(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_14, x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(x_5);
x_22 = lean_box(x_7);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___boxed), 14, 9);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_19);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_3);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_21);
lean_closure_set(x_23, 7, x_1);
lean_closure_set(x_23, 8, x_22);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_23, x_25, x_8, x_9, x_10, x_11, x_18);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0(x_1, x_2, x_15, x_4, x_5, x_6, x_16, x_8, x_17, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_18;
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
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_simp", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_20 = l_Lean_Meta_mkAuxLemma(x_1, x_18, x_17, x_19, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_21);
x_23 = l_Lean_Expr_const___override(x_21, x_3);
x_24 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
x_25 = lean_box(0);
x_26 = l_Lean_Expr_const___override(x_21, x_25);
x_27 = lean_box(0);
x_28 = lean_box(x_5);
lean_inc(x_6);
lean_inc(x_4);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed), 12, 7);
lean_closure_set(x_29, 0, x_4);
lean_closure_set(x_29, 1, x_23);
lean_closure_set(x_29, 2, x_24);
lean_closure_set(x_29, 3, x_26);
lean_closure_set(x_29, 4, x_28);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_27);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_29, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_8, x_31);
x_7 = x_16;
x_8 = x_33;
x_13 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_21 = l_Lean_Meta_mkAuxLemma(x_1, x_19, x_18, x_20, x_2, x_2, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_22);
x_24 = l_Lean_Expr_const___override(x_22, x_3);
x_25 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
x_26 = lean_box(0);
x_27 = l_Lean_Expr_const___override(x_22, x_26);
x_28 = lean_box(0);
x_29 = lean_box(x_5);
lean_inc(x_6);
lean_inc(x_4);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed), 12, 7);
lean_closure_set(x_30, 0, x_4);
lean_closure_set(x_30, 1, x_24);
lean_closure_set(x_30, 2, x_25);
lean_closure_set(x_30, 3, x_27);
lean_closure_set(x_30, 4, x_29);
lean_closure_set(x_30, 5, x_6);
lean_closure_set(x_30, 6, x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_30, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_push(x_9, x_32);
x_35 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_34, x_10, x_11, x_12, x_13, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpTheoremFromConst___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpTheoremFromConst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromConst(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_simpGlobalConfig;
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_inc(x_13);
x_20 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_13, x_19);
lean_inc(x_20);
lean_inc(x_1);
x_21 = l_Lean_Expr_const___override(x_1, x_20);
lean_ctor_set(x_5, 0, x_15);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = lean_infer_type(x_21, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_23, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_27 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(x_23, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_1);
x_30 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 1, x_3);
if (x_3 == 0)
{
uint8_t x_44; 
x_44 = lean_unbox(x_28);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
x_45 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
x_46 = l_Lean_Expr_const___override(x_1, x_19);
x_47 = lean_box(x_2);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed), 12, 7);
lean_closure_set(x_48, 0, x_30);
lean_closure_set(x_48, 1, x_21);
lean_closure_set(x_48, 2, x_45);
lean_closure_set(x_48, 3, x_46);
lean_closure_set(x_48, 4, x_47);
lean_closure_set(x_48, 5, x_4);
lean_closure_set(x_48, 6, x_28);
x_49 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_48, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = l_Lean_Meta_mkSimpTheoremFromConst___closed__1;
x_53 = lean_array_push(x_52, x_51);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = l_Lean_Meta_mkSimpTheoremFromConst___closed__1;
x_57 = lean_array_push(x_56, x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_1);
goto block_43;
}
}
else
{
lean_dec(x_28);
lean_dec(x_1);
goto block_43;
}
block_43:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_32, x_21, x_23, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_mkSimpTheoremFromConst___closed__0;
x_37 = lean_unbox(x_31);
lean_inc(x_34);
x_38 = l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg(x_13, x_37, x_20, x_30, x_2, x_4, x_34, x_34, x_36, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_34);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_27);
if (x_63 == 0)
{
return x_27;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_27, 0);
x_65 = lean_ctor_get(x_27, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_27);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_25);
if (x_67 == 0)
{
return x_25;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_25, 0);
x_69 = lean_ctor_get(x_25, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_25);
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
lean_dec(x_5);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_22);
if (x_71 == 0)
{
return x_22;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_22, 0);
x_73 = lean_ctor_get(x_22, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_22);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_ctor_get(x_5, 2);
x_78 = lean_ctor_get(x_5, 3);
x_79 = lean_ctor_get(x_5, 4);
x_80 = lean_ctor_get(x_5, 5);
x_81 = lean_ctor_get(x_5, 6);
x_82 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_83 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_5);
x_84 = lean_box(0);
lean_inc(x_13);
x_85 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_13, x_84);
lean_inc(x_85);
lean_inc(x_1);
x_86 = l_Lean_Expr_const___override(x_1, x_85);
x_87 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_87, 0, x_15);
lean_ctor_set(x_87, 1, x_76);
lean_ctor_set(x_87, 2, x_77);
lean_ctor_set(x_87, 3, x_78);
lean_ctor_set(x_87, 4, x_79);
lean_ctor_set(x_87, 5, x_80);
lean_ctor_set(x_87, 6, x_81);
lean_ctor_set_uint64(x_87, sizeof(void*)*7, x_16);
lean_ctor_set_uint8(x_87, sizeof(void*)*7 + 8, x_75);
lean_ctor_set_uint8(x_87, sizeof(void*)*7 + 9, x_82);
lean_ctor_set_uint8(x_87, sizeof(void*)*7 + 10, x_83);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_87);
lean_inc(x_86);
x_88 = lean_infer_type(x_86, x_87, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_87);
lean_inc(x_89);
x_91 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_89, x_87, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_87);
lean_inc(x_89);
x_93 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(x_89, x_87, x_6, x_7, x_8, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_1);
x_96 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 1, x_3);
if (x_3 == 0)
{
uint8_t x_110; 
x_110 = lean_unbox(x_94);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_89);
lean_dec(x_85);
lean_dec(x_13);
x_111 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
x_112 = l_Lean_Expr_const___override(x_1, x_84);
x_113 = lean_box(x_2);
x_114 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed), 12, 7);
lean_closure_set(x_114, 0, x_96);
lean_closure_set(x_114, 1, x_86);
lean_closure_set(x_114, 2, x_111);
lean_closure_set(x_114, 3, x_112);
lean_closure_set(x_114, 4, x_113);
lean_closure_set(x_114, 5, x_4);
lean_closure_set(x_114, 6, x_94);
x_115 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_114, x_87, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Meta_mkSimpTheoremFromConst___closed__1;
x_120 = lean_array_push(x_119, x_116);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_124 = x_115;
} else {
 lean_dec_ref(x_115);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_dec(x_94);
lean_dec(x_1);
goto block_109;
}
}
else
{
lean_dec(x_94);
lean_dec(x_1);
goto block_109;
}
block_109:
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_97 = lean_box(1);
x_98 = lean_unbox(x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_87);
x_99 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_98, x_86, x_89, x_87, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Meta_mkSimpTheoremFromConst___closed__0;
x_103 = lean_unbox(x_97);
lean_inc(x_100);
x_104 = l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg(x_13, x_103, x_85, x_96, x_2, x_4, x_100, x_100, x_102, x_87, x_6, x_7, x_8, x_101);
lean_dec(x_100);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_96);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_126 = lean_ctor_get(x_93, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_93, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_128 = x_93;
} else {
 lean_dec_ref(x_93);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_130 = lean_ctor_get(x_91, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_91, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_132 = x_91;
} else {
 lean_dec_ref(x_91);
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
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_134 = lean_ctor_get(x_88, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_88, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_136 = x_88;
} else {
 lean_dec_ref(x_88);
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
else
{
uint8_t x_138; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_10);
if (x_138 == 0)
{
return x_10;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_10, 0);
x_140 = lean_ctor_get(x_10, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_10);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0(x_1, x_16, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___redArg(x_1, x_15, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0(x_1, x_18, x_3, x_4, x_5, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_mkSimpTheoremFromConst(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constant expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorem_getValue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SimpTheorem_getValue___closed__2;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(1776u);
x_4 = l_Lean_Meta_SimpTheorem_getValue___closed__1;
x_5 = l_Lean_Meta_SimpTheorem_getValue___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_77; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_77 = l_Lean_Expr_isConst(x_8);
if (x_77 == 0)
{
x_9 = x_77;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = l_Array_isEmpty___redArg(x_7);
x_9 = x_78;
goto block_76;
}
block_76:
{
if (x_9 == 0)
{
size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_size(x_7);
x_11 = 0;
lean_inc(x_7);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(x_10, x_11, x_7, x_2, x_3, x_4, x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Expr_instantiateLevelParamsArray(x_8, x_7, x_14);
lean_dec(x_8);
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
x_18 = l_Lean_Expr_instantiateLevelParamsArray(x_8, x_7, x_16);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Lean_Expr_constName_x21(x_8);
x_21 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_List_isEmpty___redArg(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_21);
x_27 = lean_box(0);
x_28 = l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(x_25, x_27, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_8) == 4)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = l_ptrEqList___redArg(x_32, x_30);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_8);
x_34 = l_Lean_Expr_const___override(x_31, x_30);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_8);
return x_28;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
x_39 = l_ptrEqList___redArg(x_38, x_35);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
x_40 = l_Lean_Expr_const___override(x_37, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
lean_dec(x_44);
x_45 = l_Lean_Meta_SimpTheorem_getValue___closed__3;
x_46 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_45);
lean_ctor_set(x_28, 0, x_46);
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = l_Lean_Meta_SimpTheorem_getValue___closed__3;
x_49 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_8);
return x_21;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_21, 0);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_21);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_List_isEmpty___redArg(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
x_56 = l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(x_53, x_55, x_2, x_3, x_4, x_5, x_52);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
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
x_60 = lean_ctor_get(x_8, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_8, 1);
lean_inc(x_61);
x_62 = l_ptrEqList___redArg(x_61, x_57);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
x_63 = l_Lean_Expr_const___override(x_60, x_57);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_60);
lean_dec(x_57);
if (lean_is_scalar(x_59)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_59;
}
lean_ctor_set(x_65, 0, x_8);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_8);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_67 = x_56;
} else {
 lean_dec_ref(x_56);
 x_67 = lean_box(0);
}
x_68 = l_Lean_Meta_SimpTheorem_getValue___closed__3;
x_69 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_53);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_8);
lean_ctor_set(x_71, 1, x_52);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_21);
if (x_72 == 0)
{
return x_21;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_21, 0);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_21);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_14, x_1, x_9, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_mk(x_17);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(x_19, x_20, x_18);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_array_mk(x_22);
x_25 = lean_array_size(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(x_25, x_26, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(x_4, x_5, x_3);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_8, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_16, x_2, x_16, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_8, x_7, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_24 = lean_array_uset(x_21, x_7, x_18);
x_7 = x_23;
x_8 = x_24;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
static uint64_t _init_l_Lean_Meta_mkSimpTheoremFromExpr___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(2);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isConst(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint64_t x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; 
x_19 = lean_box(2);
x_20 = lean_unbox(x_19);
lean_ctor_set_uint8(x_14, 9, x_20);
x_21 = 2;
x_22 = lean_uint64_shift_right(x_15, x_21);
x_23 = lean_uint64_shift_left(x_22, x_21);
x_24 = l_Lean_Meta_mkSimpTheoremFromExpr___closed__0;
x_25 = lean_uint64_lor(x_23, x_24);
lean_ctor_set(x_8, 0, x_14);
lean_ctor_set_uint64(x_8, sizeof(void*)*7, x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(1);
x_30 = lean_array_size(x_27);
x_31 = 0;
x_32 = lean_unbox(x_29);
x_33 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0(x_1, x_2, x_5, x_6, x_32, x_30, x_31, x_27, x_8, x_9, x_10, x_11, x_28);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; lean_object* x_63; 
x_38 = lean_ctor_get_uint8(x_14, 0);
x_39 = lean_ctor_get_uint8(x_14, 1);
x_40 = lean_ctor_get_uint8(x_14, 2);
x_41 = lean_ctor_get_uint8(x_14, 3);
x_42 = lean_ctor_get_uint8(x_14, 4);
x_43 = lean_ctor_get_uint8(x_14, 5);
x_44 = lean_ctor_get_uint8(x_14, 6);
x_45 = lean_ctor_get_uint8(x_14, 7);
x_46 = lean_ctor_get_uint8(x_14, 8);
x_47 = lean_ctor_get_uint8(x_14, 10);
x_48 = lean_ctor_get_uint8(x_14, 11);
x_49 = lean_ctor_get_uint8(x_14, 12);
x_50 = lean_ctor_get_uint8(x_14, 13);
x_51 = lean_ctor_get_uint8(x_14, 14);
x_52 = lean_ctor_get_uint8(x_14, 15);
x_53 = lean_ctor_get_uint8(x_14, 16);
x_54 = lean_ctor_get_uint8(x_14, 17);
lean_dec(x_14);
x_55 = lean_box(2);
x_56 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_56, 0, x_38);
lean_ctor_set_uint8(x_56, 1, x_39);
lean_ctor_set_uint8(x_56, 2, x_40);
lean_ctor_set_uint8(x_56, 3, x_41);
lean_ctor_set_uint8(x_56, 4, x_42);
lean_ctor_set_uint8(x_56, 5, x_43);
lean_ctor_set_uint8(x_56, 6, x_44);
lean_ctor_set_uint8(x_56, 7, x_45);
lean_ctor_set_uint8(x_56, 8, x_46);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, 9, x_57);
lean_ctor_set_uint8(x_56, 10, x_47);
lean_ctor_set_uint8(x_56, 11, x_48);
lean_ctor_set_uint8(x_56, 12, x_49);
lean_ctor_set_uint8(x_56, 13, x_50);
lean_ctor_set_uint8(x_56, 14, x_51);
lean_ctor_set_uint8(x_56, 15, x_52);
lean_ctor_set_uint8(x_56, 16, x_53);
lean_ctor_set_uint8(x_56, 17, x_54);
x_58 = 2;
x_59 = lean_uint64_shift_right(x_15, x_58);
x_60 = lean_uint64_shift_left(x_59, x_58);
x_61 = l_Lean_Meta_mkSimpTheoremFromExpr___closed__0;
x_62 = lean_uint64_lor(x_60, x_61);
lean_ctor_set(x_8, 0, x_56);
lean_ctor_set_uint64(x_8, sizeof(void*)*7, x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_63 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; uint8_t x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(1);
x_67 = lean_array_size(x_64);
x_68 = 0;
x_69 = lean_unbox(x_66);
x_70 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0(x_1, x_2, x_5, x_6, x_69, x_67, x_68, x_64, x_8, x_9, x_10, x_11, x_65);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
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
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; 
x_75 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_76 = lean_ctor_get(x_8, 1);
x_77 = lean_ctor_get(x_8, 2);
x_78 = lean_ctor_get(x_8, 3);
x_79 = lean_ctor_get(x_8, 4);
x_80 = lean_ctor_get(x_8, 5);
x_81 = lean_ctor_get(x_8, 6);
x_82 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_83 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_8);
x_84 = lean_ctor_get_uint8(x_14, 0);
x_85 = lean_ctor_get_uint8(x_14, 1);
x_86 = lean_ctor_get_uint8(x_14, 2);
x_87 = lean_ctor_get_uint8(x_14, 3);
x_88 = lean_ctor_get_uint8(x_14, 4);
x_89 = lean_ctor_get_uint8(x_14, 5);
x_90 = lean_ctor_get_uint8(x_14, 6);
x_91 = lean_ctor_get_uint8(x_14, 7);
x_92 = lean_ctor_get_uint8(x_14, 8);
x_93 = lean_ctor_get_uint8(x_14, 10);
x_94 = lean_ctor_get_uint8(x_14, 11);
x_95 = lean_ctor_get_uint8(x_14, 12);
x_96 = lean_ctor_get_uint8(x_14, 13);
x_97 = lean_ctor_get_uint8(x_14, 14);
x_98 = lean_ctor_get_uint8(x_14, 15);
x_99 = lean_ctor_get_uint8(x_14, 16);
x_100 = lean_ctor_get_uint8(x_14, 17);
if (lean_is_exclusive(x_14)) {
 x_101 = x_14;
} else {
 lean_dec_ref(x_14);
 x_101 = lean_box(0);
}
x_102 = lean_box(2);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 0, 18);
} else {
 x_103 = x_101;
}
lean_ctor_set_uint8(x_103, 0, x_84);
lean_ctor_set_uint8(x_103, 1, x_85);
lean_ctor_set_uint8(x_103, 2, x_86);
lean_ctor_set_uint8(x_103, 3, x_87);
lean_ctor_set_uint8(x_103, 4, x_88);
lean_ctor_set_uint8(x_103, 5, x_89);
lean_ctor_set_uint8(x_103, 6, x_90);
lean_ctor_set_uint8(x_103, 7, x_91);
lean_ctor_set_uint8(x_103, 8, x_92);
x_104 = lean_unbox(x_102);
lean_ctor_set_uint8(x_103, 9, x_104);
lean_ctor_set_uint8(x_103, 10, x_93);
lean_ctor_set_uint8(x_103, 11, x_94);
lean_ctor_set_uint8(x_103, 12, x_95);
lean_ctor_set_uint8(x_103, 13, x_96);
lean_ctor_set_uint8(x_103, 14, x_97);
lean_ctor_set_uint8(x_103, 15, x_98);
lean_ctor_set_uint8(x_103, 16, x_99);
lean_ctor_set_uint8(x_103, 17, x_100);
x_105 = 2;
x_106 = lean_uint64_shift_right(x_15, x_105);
x_107 = lean_uint64_shift_left(x_106, x_105);
x_108 = l_Lean_Meta_mkSimpTheoremFromExpr___closed__0;
x_109 = lean_uint64_lor(x_107, x_108);
x_110 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_76);
lean_ctor_set(x_110, 2, x_77);
lean_ctor_set(x_110, 3, x_78);
lean_ctor_set(x_110, 4, x_79);
lean_ctor_set(x_110, 5, x_80);
lean_ctor_set(x_110, 6, x_81);
lean_ctor_set_uint64(x_110, sizeof(void*)*7, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 8, x_75);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 9, x_82);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 10, x_83);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_110);
x_111 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_4, x_110, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; size_t x_116; uint8_t x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_box(1);
x_115 = lean_array_size(x_112);
x_116 = 0;
x_117 = lean_unbox(x_114);
x_118 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0(x_1, x_2, x_5, x_6, x_117, x_115, x_116, x_112, x_110, x_9, x_10, x_11, x_113);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_110);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_123 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_124 = l_Lean_Meta_mkSimpTheoremFromConst(x_123, x_5, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
return x_124;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpTheoremFromExpr_spec__0(x_1, x_2, x_14, x_4, x_15, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremFromExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_mkSimpTheoremFromExpr(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorem___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpEntry___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Environment_isProjectionFn(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Environment_isProjectionFn(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_ignoreEquations(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_5 = l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_isReducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__2(x_1, x_2, x_3, x_7);
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isProjectionFn___at___Lean_Meta_Simp_ignoreEquations_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_ignoreEquations___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_ignoreEquations(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lean_Meta_hasSmartUnfoldingDecl(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_free_object(x_4);
x_10 = l_Lean_Meta_isRecursiveDefinition___redArg(x_1, x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(1);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_box(x_9);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_box(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = l_Lean_Meta_hasSmartUnfoldingDecl(x_28, x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Meta_isRecursiveDefinition___redArg(x_1, x_2, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = lean_box(1);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_box(x_29);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_box(x_29);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_unfoldEvenWithEqns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_unfoldEvenWithEqns(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_nat_dec_lt(x_9, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_35; uint8_t x_36; 
x_19 = lean_array_fget(x_1, x_9);
x_35 = lean_unsigned_to_nat(100u);
x_36 = lean_nat_dec_lt(x_35, x_4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_nat_sub(x_35, x_9);
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_nat_add(x_9, x_5);
x_39 = lean_nat_dec_eq(x_38, x_4);
lean_dec(x_38);
if (x_39 == 0)
{
lean_inc(x_5);
x_20 = x_5;
goto block_34;
}
else
{
lean_inc(x_6);
x_20 = x_6;
goto block_34;
}
}
block_34:
{
lean_object* x_21; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_mkSimpTheoremFromConst(x_19, x_2, x_3, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_size(x_22);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0(x_24, x_25, x_22);
x_27 = l_Array_append___redArg(x_8, x_26);
lean_dec(x_26);
x_28 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_8 = x_27;
x_9 = x_28;
x_14 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_nat_dec_lt(x_9, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_35; uint8_t x_36; 
x_19 = lean_array_fget(x_1, x_9);
x_35 = lean_unsigned_to_nat(100u);
x_36 = lean_nat_dec_lt(x_35, x_4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_nat_sub(x_35, x_9);
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_nat_add(x_9, x_5);
x_39 = lean_nat_dec_eq(x_38, x_4);
lean_dec(x_38);
if (x_39 == 0)
{
lean_inc(x_5);
x_20 = x_5;
goto block_34;
}
else
{
lean_inc(x_6);
x_20 = x_6;
goto block_34;
}
}
block_34:
{
lean_object* x_21; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_mkSimpTheoremFromConst(x_19, x_2, x_3, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_size(x_22);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0(x_24, x_25, x_22);
x_27 = l_Array_append___redArg(x_8, x_26);
lean_dec(x_26);
x_28 = lean_nat_add(x_9, x_16);
x_29 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_28, x_10, x_11, x_12, x_13, x_23);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unbox(x_9);
lean_dec(x_9);
x_12 = lean_unbox(x_10);
lean_dec(x_10);
x_13 = l_Lean_beqConstantKind____x40_Lean_Environment___hyg_1543_(x_11, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'simp', definition with exposed body expected: ", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpEntryOfDeclToUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_88; 
lean_inc(x_1);
x_88 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_5, x_90);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0;
x_97 = l_Lean_ConstantInfo_isDefinition(x_89);
lean_dec(x_89);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_inc(x_1);
x_98 = l_Lean_getOriginalConstKind_x3f(x_95, x_1);
x_99 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1;
x_100 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3(x_98, x_99);
if (x_100 == 0)
{
lean_free_object(x_91);
x_7 = x_96;
x_8 = x_2;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_94;
goto block_87;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3;
x_102 = l_Lean_MessageData_ofConstName(x_1, x_97);
lean_ctor_set_tag(x_91, 7);
lean_ctor_set(x_91, 1, x_102);
lean_ctor_set(x_91, 0, x_101);
x_103 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_104, x_2, x_3, x_4, x_5, x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_dec(x_95);
lean_free_object(x_91);
x_7 = x_96;
x_8 = x_2;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_94;
goto block_87;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_91, 0);
x_111 = lean_ctor_get(x_91, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_91);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0;
x_114 = l_Lean_ConstantInfo_isDefinition(x_89);
lean_dec(x_89);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_inc(x_1);
x_115 = l_Lean_getOriginalConstKind_x3f(x_112, x_1);
x_116 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1;
x_117 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3(x_115, x_116);
if (x_117 == 0)
{
x_7 = x_113;
x_8 = x_2;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_111;
goto block_87;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3;
x_119 = l_Lean_MessageData_ofConstName(x_1, x_114);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Meta_ppOrigin___redArg___closed__2;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_122, x_2, x_3, x_4, x_5, x_111);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_dec(x_112);
x_7 = x_113;
x_8 = x_2;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_111;
goto block_87;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_88);
if (x_128 == 0)
{
return x_88;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_88, 0);
x_130 = lean_ctor_get(x_88, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_88);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_87:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Simp_ignoreEquations(x_1, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_17 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_array_push(x_7, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_box(1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get_size(x_29);
x_33 = lean_unsigned_to_nat(1u);
lean_inc(x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_unbox(x_30);
x_36 = lean_unbox(x_14);
lean_dec(x_14);
lean_inc(x_11);
x_37 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg(x_29, x_35, x_36, x_32, x_33, x_31, x_34, x_7, x_31, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_29);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_1);
x_40 = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(x_1, x_11, x_39);
lean_dec(x_11);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_free_object(x_18);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
lean_ctor_set(x_18, 0, x_1);
x_49 = lean_array_push(x_38, x_18);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
lean_ctor_set(x_18, 0, x_1);
x_51 = lean_array_push(x_38, x_18);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
lean_free_object(x_18);
lean_dec(x_11);
lean_dec(x_1);
return x_37;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_18, 0);
lean_inc(x_53);
lean_dec(x_18);
x_54 = lean_box(1);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_53);
x_57 = lean_unsigned_to_nat(1u);
lean_inc(x_56);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_unbox(x_54);
x_60 = lean_unbox(x_14);
lean_dec(x_14);
lean_inc(x_11);
x_61 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg(x_53, x_59, x_60, x_56, x_57, x_55, x_58, x_7, x_55, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_53);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_1);
x_64 = l_Lean_Meta_Simp_unfoldEvenWithEqns___redArg(x_1, x_11, x_63);
lean_dec(x_11);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_73 = lean_array_push(x_62, x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
else
{
lean_dec(x_11);
lean_dec(x_1);
return x_61;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_17);
if (x_75 == 0)
{
return x_17;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_17, 0);
x_77 = lean_ctor_get(x_17, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_17);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_79 = !lean_is_exclusive(x_13);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_13, 0);
lean_dec(x_80);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_1);
x_82 = lean_array_push(x_7, x_81);
lean_ctor_set(x_13, 0, x_82);
return x_13;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_dec(x_13);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_1);
x_85 = lean_array_push(x_7, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___redArg(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1_spec__1(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___redArg(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__1(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_mkSimpEntryOfDeclToUnfold_spec__3(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__1;
x_2 = l_Lean_Meta_instInhabitedSimpTheorems___closed__0;
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__3;
x_2 = l_Lean_Meta_instInhabitedSimpTheorems___closed__2;
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__8;
x_2 = l_Lean_Meta_instInhabitedSimpTheorems___closed__7;
x_3 = l_Lean_Meta_instInhabitedSimpTheorems___closed__6;
x_4 = l_Lean_Meta_instInhabitedSimpTheorems___closed__5;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpTheorems___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; lean_object* x_8; 
x_3 = l_Lean_Meta_instInhabitedSimpTheorems___closed__0;
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_11 == 0)
{
lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_Lean_Name_hash___override(x_12);
lean_dec(x_12);
x_14 = 13;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_4 = x_15;
goto block_7;
}
else
{
lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = 11;
x_19 = lean_uint64_mix_hash(x_17, x_18);
x_4 = x_19;
goto block_7;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_8 = x_20;
goto block_10;
}
block_7:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(x_3, x_1, x_5, x_2);
return x_6;
}
block_10:
{
uint64_t x_9; 
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_4 = x_9;
goto block_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_11; 
x_4 = l_Lean_Meta_instInhabitedSimpTheorems___closed__0;
x_5 = l_Lean_Meta_instInhabitedSimpTheorems___closed__1;
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = l_Lean_Name_hash___override(x_15);
lean_dec(x_15);
x_17 = 13;
x_18 = lean_uint64_mix_hash(x_16, x_17);
x_6 = x_18;
goto block_10;
}
else
{
lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = l_Lean_Name_hash___override(x_19);
lean_dec(x_19);
x_21 = 11;
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_6 = x_22;
goto block_10;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_11 = x_23;
goto block_13;
}
block_10:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_8, x_2, x_3);
return x_9;
}
block_13:
{
uint64_t x_12; 
x_12 = l_Lean_Name_hash___override(x_11);
lean_dec(x_11);
x_6 = x_12;
goto block_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 1, x_6);
x_9 = l_Lean_Meta_SimpTheorems_eraseCore(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
return x_5;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
x_8 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_4, x_2);
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_6, x_2, x_9);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_11);
x_12 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(x_5, x_11);
lean_inc(x_7);
lean_ctor_set(x_1, 4, x_10);
lean_ctor_set(x_1, 3, x_12);
lean_ctor_set(x_1, 2, x_8);
x_13 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
return x_1;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
return x_1;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(x_18, x_14, x_19, x_20, x_1);
lean_dec(x_14);
return x_21;
}
}
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_1, 4, x_10);
lean_ctor_set(x_1, 2, x_8);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_ctor_get(x_1, 4);
x_27 = lean_ctor_get(x_1, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
lean_inc(x_2);
x_28 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_24, x_2);
x_29 = lean_box(0);
lean_inc(x_2);
x_30 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_26, x_2, x_29);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_31);
x_32 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(x_25, x_31);
lean_inc(x_27);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_27);
x_34 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_27, x_31);
if (lean_obj_tag(x_34) == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
return x_33;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_37, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
return x_33;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_42 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(x_39, x_35, x_40, x_41, x_33);
lean_dec(x_35);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_22);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_43, 2, x_28);
lean_ctor_set(x_43, 3, x_25);
lean_ctor_set(x_43, 4, x_30);
lean_ctor_set(x_43, 5, x_27);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_8; lean_object* x_10; lean_object* x_11; lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_2, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_24 = lean_name_eq(x_20, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
x_8 = x_24;
goto block_9;
}
else
{
if (x_21 == 0)
{
if (x_23 == 0)
{
x_8 = x_24;
goto block_9;
}
else
{
goto block_7;
}
}
else
{
x_8 = x_23;
goto block_9;
}
}
}
else
{
lean_dec(x_16);
goto block_7;
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
goto block_7;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_3, 0);
x_17 = x_25;
goto block_19;
}
}
block_19:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_10 = x_17;
x_11 = x_18;
goto block_13;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
block_9:
{
if (x_8 == 0)
{
goto block_7;
}
else
{
lean_dec(x_2);
return x_8;
}
}
block_13:
{
uint8_t x_12; 
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_11);
x_8 = x_12;
goto block_9;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 1);
lean_dec(x_11);
x_20 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
return x_20;
}
else
{
if (x_17 == 0)
{
if (x_19 == 0)
{
return x_20;
}
else
{
return x_17;
}
}
else
{
return x_19;
}
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_11);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_3, 0);
x_12 = x_25;
goto block_15;
}
}
block_15:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
case 1:
{
lean_object* x_26; size_t x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_usize_shift_right(x_2, x_6);
x_1 = x_26;
x_2 = x_27;
goto _start;
}
default: 
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(x_31, x_32, x_3);
lean_dec(x_31);
return x_33;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_10 == 0)
{
lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_Name_hash___override(x_11);
x_13 = 13;
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_3 = x_14;
goto block_6;
}
else
{
lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = l_Lean_Name_hash___override(x_15);
x_17 = 11;
x_18 = lean_uint64_mix_hash(x_16, x_17);
x_3 = x_18;
goto block_6;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 0);
x_7 = x_19;
goto block_9;
}
block_6:
{
size_t x_4; uint8_t x_5; 
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
block_9:
{
uint64_t x_8; 
x_8 = l_Lean_Name_hash___override(x_7);
x_3 = x_8;
goto block_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_3, x_2);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unerase(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
x_5 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_4, x_2);
lean_ctor_set(x_1, 4, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_10, x_2);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addSimpTheorem_updateLemmaNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_expr_eqv(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_nat_add(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_shiftr(x_9, x_10);
lean_dec(x_9);
x_12 = lean_array_fget(x_5, x_11);
x_13 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_12, x_6);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_6, x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
x_15 = lean_array_get_size(x_5);
x_16 = lean_nat_dec_lt(x_11, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_5, x_11, x_20);
x_22 = lean_nat_add(x_1, x_10);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(x_2, x_3, x_22, x_18);
lean_dec(x_22);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_4);
x_24 = lean_array_fset(x_21, x_11, x_12);
lean_dec(x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_5, x_11, x_26);
x_28 = lean_nat_add(x_1, x_10);
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(x_2, x_3, x_28, x_25);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_fset(x_27, x_11, x_30);
lean_dec(x_11);
return x_31;
}
}
}
else
{
lean_dec(x_12);
x_8 = x_11;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
x_33 = lean_nat_dec_eq(x_11, x_7);
if (x_33 == 0)
{
lean_dec(x_7);
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_8);
x_35 = lean_nat_add(x_1, x_10);
x_36 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(x_2, x_3, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
x_39 = lean_array_get_size(x_5);
x_40 = lean_array_push(x_5, x_37);
x_41 = l_Array_insertIdx_loop___redArg(x_38, x_40, x_39);
lean_dec(x_38);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(x_2, x_3, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(x_2, x_3, x_10, x_7);
lean_dec(x_10);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(x_2, x_3, x_14, x_12);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_8);
x_11 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(x_6, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(x_10, x_6);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_array_fset(x_5, x_8, x_14);
x_16 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_10);
x_17 = lean_array_fset(x_15, x_8, x_16);
return x_17;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
x_20 = lean_array_fget(x_5, x_19);
x_21 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(x_20, x_6);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(x_6, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_19, x_7);
lean_dec(x_7);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(0);
x_25 = lean_array_fset(x_5, x_19, x_24);
x_26 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_20);
x_27 = lean_array_fset(x_25, x_19, x_26);
lean_dec(x_19);
return x_27;
}
}
else
{
if (x_21 == 0)
{
lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_7);
x_28 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_19);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_lt(x_19, x_7);
lean_dec(x_7);
if (x_29 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_box(0);
x_31 = lean_array_fset(x_5, x_19, x_30);
x_32 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_20);
x_33 = lean_array_fset(x_31, x_19, x_32);
lean_dec(x_19);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_7);
x_34 = lean_box(0);
x_35 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_34);
x_36 = lean_array_push(x_5, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_37 == 0)
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_fset(x_5, x_8, x_38);
x_40 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_10);
x_41 = lean_array_fset(x_39, x_8, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
x_42 = lean_box(0);
x_43 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_42);
x_44 = lean_array_push(x_5, x_43);
x_45 = l_Array_insertIdx_loop___redArg(x_8, x_44, x_7);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
x_46 = lean_box(0);
x_47 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_46);
x_48 = lean_array_push(x_5, x_47);
return x_48;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpTheoremFromConst___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0(x_6, x_2);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_1, x_3);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_11, x_7, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 1, x_14);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__0(x_15, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_1, x_3);
x_22 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0;
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_21, x_16, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.insertCore", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid key sequence", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__2;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(482u);
x_4 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__1;
x_5 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___redArg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(x_2, x_3, x_9);
x_11 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(x_2, x_3, x_13, x_12);
x_15 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(x_1, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__3;
x_17 = l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addSimpTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
lean_inc(x_2);
x_5 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_2);
x_9 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(x_7, x_3, x_2);
lean_dec(x_3);
x_10 = l_Lean_Meta_SimpTheorems_addSimpTheorem_updateLemmaNames(x_2, x_8);
lean_ctor_set(x_5, 2, x_10);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
lean_inc(x_2);
x_17 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(x_11, x_3, x_2);
lean_dec(x_3);
x_18 = l_Lean_Meta_SimpTheorems_addSimpTheorem_updateLemmaNames(x_2, x_13);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
lean_inc(x_2);
x_23 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(x_21, x_3, x_2);
lean_dec(x_3);
x_24 = l_Lean_Meta_SimpTheorems_addSimpTheorem_updateLemmaNames(x_2, x_22);
lean_ctor_set(x_5, 2, x_24);
lean_ctor_set(x_5, 1, x_23);
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_ctor_get(x_5, 3);
x_29 = lean_ctor_get(x_5, 4);
x_30 = lean_ctor_get(x_5, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
lean_inc(x_2);
x_31 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(x_26, x_3, x_2);
lean_dec(x_3);
x_32 = l_Lean_Meta_SimpTheorems_addSimpTheorem_updateLemmaNames(x_2, x_27);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_30);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SimpTheorems_addSimpTheorem(x_1, x_2);
return x_3;
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
x_6 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_4, x_2, x_5);
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
x_14 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_10, x_2, x_13);
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
x_6 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_4, x_2, x_5);
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
x_14 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_10, x_2, x_13);
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
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(x_3, x_2);
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
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(x_3, x_2);
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
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_3, x_2);
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
x_6 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_5, x_2, x_3);
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
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_12, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_18; 
x_9 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3;
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_10 = x_18;
goto block_17;
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_MessageData_ofName(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__1;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_logWarning___redArg(x_1, x_2, x_3, x_4, x_14);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_15, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Origin_converse(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_5);
x_13 = l_Lean_Meta_SimpTheorems_isLemma(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_3);
x_17 = l_Lean_Meta_SimpTheorems_eraseCore(x_5, x_12);
x_18 = lean_apply_2(x_2, lean_box(0), x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_6);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_8);
lean_closure_set(x_11, 5, x_10);
lean_closure_set(x_11, 6, x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__2), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_8);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_12);
lean_inc(x_5);
x_21 = l_Lean_Meta_SimpTheorems_isLemma(x_5, x_6);
if (x_21 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_inc(x_5);
x_23 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_5, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
x_25 = l_Lean_Meta_instInhabitedSimpTheorems___closed__2;
x_26 = l_Lean_Meta_instInhabitedSimpTheorems___closed__3;
x_27 = l_Lean_PersistentHashMap_contains___redArg(x_25, x_26, x_24, x_22);
x_14 = x_27;
goto block_20;
}
else
{
lean_dec(x_22);
x_14 = x_23;
goto block_20;
}
}
else
{
x_14 = x_21;
goto block_20;
}
}
else
{
x_14 = x_21;
goto block_20;
}
block_20:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_9, lean_box(0), x_15);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_8);
x_18 = l_Lean_Meta_SimpTheorems_eraseCore(x_5, x_6);
x_19 = lean_apply_2(x_9, lean_box(0), x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_erase___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addSimpEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_SimpTheorems_addSimpTheorem(x_1, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_uneraseSimpEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_SimpTheorems_unerase(x_1, x_4);
return x_5;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_SimpTheorems_addSimpTheorem(x_4, x_6);
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
lean_object* x_11; 
x_11 = l_Lean_Meta_mkSimpTheoremFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_13);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_13, x_18, x_19, x_1);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_24, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_31 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_21, x_29, x_30, x_1);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_1, x_5, x_6, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_12 = l_Lean_Meta_instInhabitedSimpTheorems;
x_13 = l_Lean_ScopedEnvExtension_getState___redArg(x_12, x_1, x_10, x_11);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_19 = l_Lean_Meta_instInhabitedSimpTheorems;
x_20 = l_Lean_ScopedEnvExtension_getState___redArg(x_19, x_1, x_17, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_6, x_5);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_7);
x_14 = lean_array_uget(x_4, x_6);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_9);
lean_inc(x_1);
x_16 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(x_1, x_15, x_2, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_6, x_18);
lean_inc(x_3);
{
size_t _tmp_5 = x_19;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_10 = x_17;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_11 = _tmp_10;
}
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = l_Lean_Environment_setExporting(x_12, x_2);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_5);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
x_44 = lean_ctor_get(x_9, 6);
x_45 = lean_ctor_get(x_9, 7);
x_46 = lean_ctor_get(x_9, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_47 = l_Lean_Environment_setExporting(x_39, x_2);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_3);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_1, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
x_60 = lean_st_ref_set(x_4, x_59, x_53);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addSimpTheorem___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_addSimpTheorem___closed__6;
x_2 = l_Lean_Meta_addSimpTheorem___closed__5;
x_3 = l_Lean_Meta_addSimpTheorem___closed__4;
x_4 = l_Lean_Meta_addSimpTheorem___closed__3;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_136; 
x_136 = l_Lean_isPrivateName(x_2);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_box(1);
x_138 = lean_unbox(x_137);
x_12 = x_138;
goto block_135;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_box(0);
x_140 = lean_unbox(x_139);
x_12 = x_140;
goto block_135;
}
block_135:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_st_ref_get(x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 5);
lean_dec(x_21);
x_22 = l_Lean_Environment_setExporting(x_20, x_12);
x_23 = l_Lean_Meta_addSimpTheorem___closed__2;
lean_ctor_set(x_17, 5, x_23);
lean_ctor_set(x_17, 0, x_22);
x_24 = lean_st_ref_set(x_10, x_17, x_18);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_8, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = l_Lean_Meta_addSimpTheorem___closed__7;
lean_ctor_set(x_27, 1, x_31);
x_32 = lean_st_ref_set(x_8, x_27, x_28);
x_33 = lean_ctor_get(x_14, 0);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get_uint8(x_33, sizeof(void*)*8);
lean_dec(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_Meta_mkSimpTheoremFromConst(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = l_Lean_Meta_addSimpTheorem___lam__0(x_10, x_35, x_23, x_8, x_31, x_39, x_38);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_array_size(x_37);
x_44 = 0;
x_45 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_5, x_42, x_37, x_43, x_44, x_42, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_37);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_42);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_1);
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
x_52 = lean_box(0);
x_53 = l_Lean_Meta_addSimpTheorem___lam__0(x_10, x_35, x_23, x_8, x_31, x_52, x_51);
lean_dec(x_8);
lean_dec(x_10);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_50);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_27, 0);
x_59 = lean_ctor_get(x_27, 2);
x_60 = lean_ctor_get(x_27, 3);
x_61 = lean_ctor_get(x_27, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_27);
x_62 = l_Lean_Meta_addSimpTheorem___closed__7;
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
x_64 = lean_st_ref_set(x_8, x_63, x_28);
x_65 = lean_ctor_get(x_14, 0);
lean_inc(x_65);
lean_dec(x_14);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get_uint8(x_65, sizeof(void*)*8);
lean_dec(x_65);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l_Lean_Meta_mkSimpTheoremFromConst(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_69);
x_72 = l_Lean_Meta_addSimpTheorem___lam__0(x_10, x_67, x_23, x_8, x_62, x_71, x_70);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = lean_array_size(x_69);
x_76 = 0;
x_77 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_5, x_74, x_69, x_75, x_76, x_74, x_8, x_9, x_10, x_73);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_69);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
lean_dec(x_1);
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_68, 1);
lean_inc(x_82);
lean_dec(x_68);
x_83 = lean_box(0);
x_84 = l_Lean_Meta_addSimpTheorem___lam__0(x_10, x_67, x_23, x_8, x_62, x_83, x_82);
lean_dec(x_8);
lean_dec(x_10);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_88 = lean_ctor_get(x_17, 0);
x_89 = lean_ctor_get(x_17, 1);
x_90 = lean_ctor_get(x_17, 2);
x_91 = lean_ctor_get(x_17, 3);
x_92 = lean_ctor_get(x_17, 4);
x_93 = lean_ctor_get(x_17, 6);
x_94 = lean_ctor_get(x_17, 7);
x_95 = lean_ctor_get(x_17, 8);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_17);
x_96 = l_Lean_Environment_setExporting(x_88, x_12);
x_97 = l_Lean_Meta_addSimpTheorem___closed__2;
x_98 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_98, 2, x_90);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_92);
lean_ctor_set(x_98, 5, x_97);
lean_ctor_set(x_98, 6, x_93);
lean_ctor_set(x_98, 7, x_94);
lean_ctor_set(x_98, 8, x_95);
x_99 = lean_st_ref_set(x_10, x_98, x_18);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_st_ref_take(x_8, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 4);
lean_inc(x_107);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 lean_ctor_release(x_102, 4);
 x_108 = x_102;
} else {
 lean_dec_ref(x_102);
 x_108 = lean_box(0);
}
x_109 = l_Lean_Meta_addSimpTheorem___closed__7;
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_106);
lean_ctor_set(x_110, 4, x_107);
x_111 = lean_st_ref_set(x_8, x_110, x_103);
x_112 = lean_ctor_get(x_14, 0);
lean_inc(x_112);
lean_dec(x_14);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get_uint8(x_112, sizeof(void*)*8);
lean_dec(x_112);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_115 = l_Lean_Meta_mkSimpTheoremFromConst(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_119 = l_Lean_Meta_addSimpTheorem___lam__0(x_10, x_114, x_97, x_8, x_109, x_118, x_117);
lean_dec(x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_box(0);
x_122 = lean_array_size(x_116);
x_123 = 0;
x_124 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_5, x_121, x_116, x_122, x_123, x_121, x_8, x_9, x_10, x_120);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_116);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_9);
lean_dec(x_1);
x_128 = lean_ctor_get(x_115, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_115, 1);
lean_inc(x_129);
lean_dec(x_115);
x_130 = lean_box(0);
x_131 = l_Lean_Meta_addSimpTheorem___lam__0(x_10, x_114, x_97, x_8, x_109, x_130, x_129);
lean_dec(x_8);
lean_dec(x_10);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
 lean_ctor_set_tag(x_134, 1);
}
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_12, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_addSimpTheorem___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
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
static lean_object* _init_l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__14____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto___closed__15____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__14____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_4 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__16____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto___closed__17____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__16____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__18____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__17____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__19____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__18____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__15____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__20____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__19____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__21____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__20____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__22____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__21____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__23____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__22____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__24____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__23____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__25____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__24____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__26____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__25____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__27____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__26____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_2 = l___auto___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__27____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_;
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SimpTheorems_addSimpEntry(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSimpExt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSimpExt___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpExt___lam__0), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpExt___lam__1___boxed), 1, 0);
x_5 = l_Lean_Meta_mkSimpExt___closed__0;
x_6 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_box(0));
x_7 = l_Lean_Meta_mkSimpExt___closed__1;
x_8 = l_Lean_Meta_mkSimpExt___closed__3;
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set(x_9, 5, x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_4);
x_11 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_10, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkSimpExt___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_;
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
static lean_object* _init_l_Lean_Meta_getSimpExtension_x3f___closed__0() {
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
x_3 = l_Lean_Meta_getSimpExtension_x3f___closed__0;
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
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_1, x_21);
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
x_40 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_1, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_24);
return x_41;
}
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_SimpTheorems_addSimpEntry(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkSimpEntryOfDeclToUnfold(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_12, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(x_10, x_15, x_16, x_1);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_18);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(x_18, x_26, x_27, x_1);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_mkSimpTheoremFromExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_16, x_21, x_22, x_1);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_34 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_24, x_32, x_33, x_1);
lean_dec(x_24);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
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
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_mkSimpExt___closed__3;
x_2 = l_Lean_Meta_mkSimpExt___closed__1;
x_3 = l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__0;
x_4 = l_Lean_Meta_mkSimpExt___closed__0;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = l_Array_isEmpty___redArg(x_1);
x_11 = lean_box(1);
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_1, x_12);
x_17 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
x_18 = lean_unsigned_to_nat(1000u);
x_19 = lean_unbox(x_11);
x_20 = l_Lean_Meta_SimpTheorems_add(x_16, x_2, x_17, x_3, x_10, x_19, x_18, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_array_fset(x_1, x_12, x_23);
x_25 = lean_array_fset(x_24, x_12, x_22);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_1, x_12, x_28);
x_30 = lean_array_fset(x_29, x_12, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_1);
x_36 = l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__1;
x_37 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3;
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(1000u);
x_40 = lean_unbox(x_38);
x_41 = lean_unbox(x_11);
x_42 = l_Lean_Meta_SimpTheorems_add(x_36, x_2, x_37, x_3, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2;
x_46 = lean_array_push(x_45, x_44);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2;
x_50 = lean_array_push(x_49, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_7 = lean_box(0);
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
x_5 = l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
x_8 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_7, x_1);
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
return x_8;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(x_1, x_2, x_5, x_6);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(x_1, x_2, x_5, x_6);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(x_1, x_2, x_5, x_6);
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
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object*);
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
res = initialize_Lean_DefEqAttrib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_dsimp_useDefEqAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_dsimp_useDefEqAttr);
lean_dec_ref(res);
}l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_45_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_debug_tactic_simp_checkDefEqAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_debug_tactic_simp_checkDefEqAttr);
lean_dec_ref(res);
}l_Lean_Meta_instInhabitedOrigin___closed__0 = _init_l_Lean_Meta_instInhabitedOrigin___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedOrigin___closed__0);
l_Lean_Meta_instInhabitedOrigin = _init_l_Lean_Meta_instInhabitedOrigin();
lean_mark_persistent(l_Lean_Meta_instInhabitedOrigin);
l_Lean_Meta_reprOrigin___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_reprOrigin___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_ = _init_l_Lean_Meta_reprOrigin___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_();
lean_mark_persistent(l_Lean_Meta_reprOrigin___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_177_);
l_Lean_Meta_instReprOrigin___closed__0 = _init_l_Lean_Meta_instReprOrigin___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprOrigin___closed__0);
l_Lean_Meta_instReprOrigin = _init_l_Lean_Meta_instReprOrigin();
lean_mark_persistent(l_Lean_Meta_instReprOrigin);
l_Lean_Meta_instBEqOrigin = _init_l_Lean_Meta_instBEqOrigin();
lean_mark_persistent(l_Lean_Meta_instBEqOrigin);
l_Lean_Meta_instHashableOrigin = _init_l_Lean_Meta_instHashableOrigin();
lean_mark_persistent(l_Lean_Meta_instHashableOrigin);
l_Lean_Meta_instLTOrigin = _init_l_Lean_Meta_instLTOrigin();
lean_mark_persistent(l_Lean_Meta_instLTOrigin);
l_Lean_Meta_instInhabitedSimpTheorem___closed__0 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__0);
l_Lean_Meta_instInhabitedSimpTheorem___closed__1 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__1);
l_Lean_Meta_instInhabitedSimpTheorem___closed__2 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__2);
l_Lean_Meta_instInhabitedSimpTheorem___closed__3 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__3);
l_Lean_Meta_instInhabitedSimpTheorem___closed__4 = _init_l_Lean_Meta_instInhabitedSimpTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem___closed__4);
l_Lean_Meta_instInhabitedSimpTheorem = _init_l_Lean_Meta_instInhabitedSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___closed__7);
l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__0 = _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__0();
lean_mark_persistent(l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__0);
l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1 = _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1();
lean_mark_persistent(l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__1);
l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__2 = _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__2();
lean_mark_persistent(l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__2);
l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3 = _init_l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3();
lean_mark_persistent(l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore___closed__2);
l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0 = _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__0);
l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__1 = _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__1);
l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__2 = _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__2);
l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3 = _init_l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem___lam__1___closed__3);
l_Lean_Meta_instToFormatSimpTheorem = _init_l_Lean_Meta_instToFormatSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem);
l_Lean_Meta_ppOrigin___redArg___closed__0 = _init_l_Lean_Meta_ppOrigin___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__0);
l_Lean_Meta_ppOrigin___redArg___closed__1 = _init_l_Lean_Meta_ppOrigin___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__1);
l_Lean_Meta_ppOrigin___redArg___closed__2 = _init_l_Lean_Meta_ppOrigin___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__2);
l_Lean_Meta_ppOrigin___redArg___closed__3 = _init_l_Lean_Meta_ppOrigin___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__3);
l_Lean_Meta_ppOrigin___redArg___closed__4 = _init_l_Lean_Meta_ppOrigin___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__4);
l_Lean_Meta_ppOrigin___redArg___closed__5 = _init_l_Lean_Meta_ppOrigin___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__5);
l_Lean_Meta_ppOrigin___redArg___closed__6 = _init_l_Lean_Meta_ppOrigin___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_ppOrigin___redArg___closed__6);
l_Lean_Meta_ppSimpTheorem___redArg___lam__0___closed__0 = _init_l_Lean_Meta_ppSimpTheorem___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___redArg___lam__0___closed__0);
l_Lean_Meta_instBEqSimpTheorem = _init_l_Lean_Meta_instBEqSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instBEqSimpTheorem);
l_Lean_Meta_simpGlobalConfig___closed__0 = _init_l_Lean_Meta_simpGlobalConfig___closed__0();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig___closed__0);
l_Lean_Meta_simpGlobalConfig___closed__1 = _init_l_Lean_Meta_simpGlobalConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig___closed__1);
l_Lean_Meta_simpGlobalConfig = _init_l_Lean_Meta_simpGlobalConfig();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__0);
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
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__13);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__14);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__15);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__16);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__17 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__17);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__18);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__19 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__19);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__20);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__21 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__21();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__21);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__22);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__23);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__24);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__25 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__25();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__25);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__26);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__27);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__28 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__28();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__28);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___closed__29);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp___closed__1);
l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__0);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___closed__3);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__0);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__1);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__2);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_mkSimpTheoremFromConst_spec__0_spec__0___redArg___closed__3);
l_Lean_Meta_mkSimpTheoremFromConst___closed__0 = _init_l_Lean_Meta_mkSimpTheoremFromConst___closed__0();
lean_mark_persistent(l_Lean_Meta_mkSimpTheoremFromConst___closed__0);
l_Lean_Meta_mkSimpTheoremFromConst___closed__1 = _init_l_Lean_Meta_mkSimpTheoremFromConst___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpTheoremFromConst___closed__1);
l_Lean_Meta_SimpTheorem_getValue___closed__0 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__0();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__0);
l_Lean_Meta_SimpTheorem_getValue___closed__1 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__1);
l_Lean_Meta_SimpTheorem_getValue___closed__2 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__2);
l_Lean_Meta_SimpTheorem_getValue___closed__3 = _init_l_Lean_Meta_SimpTheorem_getValue___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpTheorem_getValue___closed__3);
l_Lean_Meta_mkSimpTheoremFromExpr___closed__0 = _init_l_Lean_Meta_mkSimpTheoremFromExpr___closed__0();
l_Lean_Meta_instInhabitedSimpEntry___closed__0 = _init_l_Lean_Meta_instInhabitedSimpEntry___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry___closed__0);
l_Lean_Meta_instInhabitedSimpEntry = _init_l_Lean_Meta_instInhabitedSimpEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry);
l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0 = _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0();
lean_mark_persistent(l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__0);
l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1 = _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__1);
l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__2 = _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__2);
l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3 = _init_l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpEntryOfDeclToUnfold___closed__3);
l_Lean_Meta_instInhabitedSimpTheorems___closed__0 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__0);
l_Lean_Meta_instInhabitedSimpTheorems___closed__1 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__1);
l_Lean_Meta_instInhabitedSimpTheorems___closed__2 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__2);
l_Lean_Meta_instInhabitedSimpTheorems___closed__3 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__3);
l_Lean_Meta_instInhabitedSimpTheorems___closed__4 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__4);
l_Lean_Meta_instInhabitedSimpTheorems___closed__5 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__5();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__5);
l_Lean_Meta_instInhabitedSimpTheorems___closed__6 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__6();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__6);
l_Lean_Meta_instInhabitedSimpTheorems___closed__7 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__7();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__7);
l_Lean_Meta_instInhabitedSimpTheorems___closed__8 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__8();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__8);
l_Lean_Meta_instInhabitedSimpTheorems___closed__9 = _init_l_Lean_Meta_instInhabitedSimpTheorems___closed__9();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems___closed__9);
l_Lean_Meta_instInhabitedSimpTheorems = _init_l_Lean_Meta_instInhabitedSimpTheorems();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems);
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___closed__1();
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__0___closed__0);
l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5___closed__0 = _init_l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0_spec__5___closed__0);
l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__0 = _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__0);
l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_SimpTheorems_addSimpTheorem_spec__0___closed__3);
l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__0 = _init_l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__0);
l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__1 = _init_l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___closed__1);
l_Lean_Meta_addSimpTheorem___closed__0 = _init_l_Lean_Meta_addSimpTheorem___closed__0();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__0);
l_Lean_Meta_addSimpTheorem___closed__1 = _init_l_Lean_Meta_addSimpTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__1);
l_Lean_Meta_addSimpTheorem___closed__2 = _init_l_Lean_Meta_addSimpTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__2);
l_Lean_Meta_addSimpTheorem___closed__3 = _init_l_Lean_Meta_addSimpTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__3);
l_Lean_Meta_addSimpTheorem___closed__4 = _init_l_Lean_Meta_addSimpTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__4);
l_Lean_Meta_addSimpTheorem___closed__5 = _init_l_Lean_Meta_addSimpTheorem___closed__5();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__5);
l_Lean_Meta_addSimpTheorem___closed__6 = _init_l_Lean_Meta_addSimpTheorem___closed__6();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__6);
l_Lean_Meta_addSimpTheorem___closed__7 = _init_l_Lean_Meta_addSimpTheorem___closed__7();
lean_mark_persistent(l_Lean_Meta_addSimpTheorem___closed__7);
l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__5____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__6____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__7____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__8____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__9____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__10____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__11____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__12____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__13____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__14____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__14____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__14____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__15____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__15____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__15____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__16____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__16____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__16____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__17____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__17____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__17____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__18____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__18____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__18____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__19____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__19____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__19____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__20____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__20____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__20____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__21____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__21____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__21____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__22____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__22____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__22____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__23____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__23____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__23____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__24____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__24____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__24____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__25____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__25____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__25____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__26____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__26____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__26____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto___closed__27____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto___closed__27____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto___closed__27____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6914_);
l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__0 = _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__0);
l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__1 = _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0___closed__1);
l_Lean_Meta_mkSimpExt___closed__0 = _init_l_Lean_Meta_mkSimpExt___closed__0();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__0);
l_Lean_Meta_mkSimpExt___closed__1 = _init_l_Lean_Meta_mkSimpExt___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__1);
l_Lean_Meta_mkSimpExt___closed__2 = _init_l_Lean_Meta_mkSimpExt___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__2);
l_Lean_Meta_mkSimpExt___closed__3 = _init_l_Lean_Meta_mkSimpExt___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSimpExt___closed__3);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_6944_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtensionMapRef);
lean_dec_ref(res);
}l_Lean_Meta_getSimpExtension_x3f___closed__0 = _init_l_Lean_Meta_getSimpExtension_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_getSimpExtension_x3f___closed__0);
l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__0 = _init_l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__0();
lean_mark_persistent(l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__0);
l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__1 = _init_l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__1);
l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2 = _init_l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheoremsArray_addTheorem___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
