// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOnSameCtor
// Imports: public import Lean.Meta.Basic import Lean.Meta.CompletionName import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CtorElim import Lean.Elab.App import Lean.Meta.SameCtorUtils
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
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_markMatcherLike(lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object**);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object**);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object**);
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Constructions.CasesOnSameCtor"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__0_value;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.mkCasesOnSameCtorHet"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__1_value;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected universe levels on `casesOn`"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__2 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__2_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtorHet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtorHet___closed__3;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__4 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__4_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtorHet___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtorHet___closed__5;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "could not apply "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " to close\n"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unifyEqns\? unexpectedly closed goal"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object**);
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "het"};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 194, 63, 63, 137, 239, 65, 92)}};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__1_value;
static const lean_string_object l_Lean_mkCasesOnSameCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.mkCasesOnSameCtor"};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__2 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__2_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___closed__3;
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_27_, 0, v_k_20_);
v___x_28_ = 0;
v___x_29_ = lean_box(0);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_28_, v___x_29_, v_type_19_, v___f_27_, v_cleanupAnnotations_21_, v___x_28_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_cleanupAnnotations_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; lean_object* v_res_56_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_49_);
v_res_56_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_47_, v_k_48_, v_cleanupAnnotations_boxed_55_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object* v_00_u03b1_57_, lean_object* v_type_58_, lean_object* v_k_59_, uint8_t v_cleanupAnnotations_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_58_, v_k_59_, v_cleanupAnnotations_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object* v_00_u03b1_67_, lean_object* v_type_68_, lean_object* v_k_69_, lean_object* v_cleanupAnnotations_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_76_; lean_object* v_res_77_; 
v_cleanupAnnotations_boxed_76_ = lean_unbox(v_cleanupAnnotations_70_);
v_res_77_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(v_00_u03b1_67_, v_type_68_, v_k_69_, v_cleanupAnnotations_boxed_76_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object* v_k_78_, lean_object* v_b_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_apply_6(v_k_78_, v_b_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object* v_k_86_, lean_object* v_b_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(v_k_86_, v_b_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object* v_name_94_, uint8_t v_bi_95_, lean_object* v_type_96_, lean_object* v_k_97_, uint8_t v_kind_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; 
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_104_, 0, v_k_97_);
v___x_105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_94_, v_bi_95_, v_type_96_, v___f_104_, v_kind_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_105_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_105_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object* v_name_122_, lean_object* v_bi_123_, lean_object* v_type_124_, lean_object* v_k_125_, lean_object* v_kind_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
uint8_t v_bi_boxed_132_; uint8_t v_kind_boxed_133_; lean_object* v_res_134_; 
v_bi_boxed_132_ = lean_unbox(v_bi_123_);
v_kind_boxed_133_ = lean_unbox(v_kind_126_);
v_res_134_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_122_, v_bi_boxed_132_, v_type_124_, v_k_125_, v_kind_boxed_133_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object* v_00_u03b1_135_, lean_object* v_name_136_, uint8_t v_bi_137_, lean_object* v_type_138_, lean_object* v_k_139_, uint8_t v_kind_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_136_, v_bi_137_, v_type_138_, v_k_139_, v_kind_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object* v_00_u03b1_147_, lean_object* v_name_148_, lean_object* v_bi_149_, lean_object* v_type_150_, lean_object* v_k_151_, lean_object* v_kind_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v_bi_boxed_158_; uint8_t v_kind_boxed_159_; lean_object* v_res_160_; 
v_bi_boxed_158_ = lean_unbox(v_bi_149_);
v_kind_boxed_159_ = lean_unbox(v_kind_152_);
v_res_160_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(v_00_u03b1_147_, v_name_148_, v_bi_boxed_158_, v_type_150_, v_k_151_, v_kind_boxed_159_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object* v_type_161_, lean_object* v_maxFVars_x3f_162_, lean_object* v_k_163_, uint8_t v_cleanupAnnotations_164_, uint8_t v_whnfType_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; 
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_171_, 0, v_k_163_);
v___x_172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_161_, v_maxFVars_x3f_162_, v___f_171_, v_cleanupAnnotations_164_, v_whnfType_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_172_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_172_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object* v_type_189_, lean_object* v_maxFVars_x3f_190_, lean_object* v_k_191_, lean_object* v_cleanupAnnotations_192_, lean_object* v_whnfType_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_199_; uint8_t v_whnfType_boxed_200_; lean_object* v_res_201_; 
v_cleanupAnnotations_boxed_199_ = lean_unbox(v_cleanupAnnotations_192_);
v_whnfType_boxed_200_ = lean_unbox(v_whnfType_193_);
v_res_201_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_189_, v_maxFVars_x3f_190_, v_k_191_, v_cleanupAnnotations_boxed_199_, v_whnfType_boxed_200_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object* v_00_u03b1_202_, lean_object* v_type_203_, lean_object* v_maxFVars_x3f_204_, lean_object* v_k_205_, uint8_t v_cleanupAnnotations_206_, uint8_t v_whnfType_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_203_, v_maxFVars_x3f_204_, v_k_205_, v_cleanupAnnotations_206_, v_whnfType_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object* v_00_u03b1_214_, lean_object* v_type_215_, lean_object* v_maxFVars_x3f_216_, lean_object* v_k_217_, lean_object* v_cleanupAnnotations_218_, lean_object* v_whnfType_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_225_; uint8_t v_whnfType_boxed_226_; lean_object* v_res_227_; 
v_cleanupAnnotations_boxed_225_ = lean_unbox(v_cleanupAnnotations_218_);
v_whnfType_boxed_226_ = lean_unbox(v_whnfType_219_);
v_res_227_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(v_00_u03b1_214_, v_type_215_, v_maxFVars_x3f_216_, v_k_217_, v_cleanupAnnotations_boxed_225_, v_whnfType_boxed_226_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object* v_name_228_, lean_object* v_levelParams_229_, lean_object* v_type_230_, lean_object* v_value_231_, lean_object* v_hints_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; uint8_t v___y_237_; uint8_t v___y_244_; lean_object* v_env_247_; uint8_t v___x_248_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_env_247_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_env_247_);
lean_dec(v___x_235_);
lean_inc_ref(v_env_247_);
v___x_248_ = l_Lean_Environment_hasUnsafe(v_env_247_, v_type_230_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Environment_hasUnsafe(v_env_247_, v_value_231_);
v___y_244_ = v___x_249_;
goto v___jp_243_;
}
else
{
lean_dec_ref(v_env_247_);
v___y_244_ = v___x_248_;
goto v___jp_243_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v_name_228_);
v___x_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_238_, 0, v_name_228_);
lean_ctor_set(v___x_238_, 1, v_levelParams_229_);
lean_ctor_set(v___x_238_, 2, v_type_230_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_name_228_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v_value_231_);
lean_ctor_set(v___x_241_, 2, v_hints_232_);
lean_ctor_set(v___x_241_, 3, v___x_240_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*4, v___y_237_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 1;
v___y_237_ = v___x_245_;
goto v___jp_236_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
v___y_237_ = v___x_246_;
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object* v_name_250_, lean_object* v_levelParams_251_, lean_object* v_type_252_, lean_object* v_value_253_, lean_object* v_hints_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_250_, v_levelParams_251_, v_type_252_, v_value_253_, v_hints_254_, v___y_255_);
lean_dec(v___y_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object* v_name_258_, lean_object* v_levelParams_259_, lean_object* v_type_260_, lean_object* v_value_261_, lean_object* v_hints_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_258_, v_levelParams_259_, v_type_260_, v_value_261_, v_hints_262_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object* v_name_269_, lean_object* v_levelParams_270_, lean_object* v_type_271_, lean_object* v_value_272_, lean_object* v_hints_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_269_, v_levelParams_270_, v_type_271_, v_value_272_, v_hints_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_280_, uint8_t v_isExporting_281_, lean_object* v___x_282_, lean_object* v___y_283_, lean_object* v___x_284_, lean_object* v_a_x3f_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_auxDeclNGen_291_; lean_object* v_traceState_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_320_; 
v___x_287_ = lean_st_ref_take(v___y_280_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_289_ = lean_ctor_get(v___x_287_, 1);
v_ngen_290_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_291_ = lean_ctor_get(v___x_287_, 3);
v_traceState_292_ = lean_ctor_get(v___x_287_, 4);
v_messages_293_ = lean_ctor_get(v___x_287_, 6);
v_infoState_294_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_295_ = lean_ctor_get(v___x_287_, 8);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_287_, 5);
lean_dec(v_unused_321_);
v___x_297_ = v___x_287_;
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Environment_setExporting(v_env_288_, v_isExporting_281_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 5, v___x_282_);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_auxDeclNGen_291_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_snapshotTasks_295_);
v___x_301_ = v_reuseFailAlloc_319_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_mctx_304_; lean_object* v_zetaDeltaFVarIds_305_; lean_object* v_postponed_306_; lean_object* v_diag_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v___x_302_ = lean_st_ref_set(v___y_280_, v___x_301_);
v___x_303_ = lean_st_ref_take(v___y_283_);
v_mctx_304_ = lean_ctor_get(v___x_303_, 0);
v_zetaDeltaFVarIds_305_ = lean_ctor_get(v___x_303_, 2);
v_postponed_306_ = lean_ctor_get(v___x_303_, 3);
v_diag_307_ = lean_ctor_get(v___x_303_, 4);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_303_, 1);
lean_dec(v_unused_318_);
v___x_309_ = v___x_303_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_diag_307_);
lean_inc(v_postponed_306_);
lean_inc(v_zetaDeltaFVarIds_305_);
lean_inc(v_mctx_304_);
lean_dec(v___x_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_284_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_mctx_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_zetaDeltaFVarIds_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_postponed_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_diag_307_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_st_ref_set(v___y_283_, v___x_312_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_322_, lean_object* v_isExporting_323_, lean_object* v___x_324_, lean_object* v___y_325_, lean_object* v___x_326_, lean_object* v_a_x3f_327_, lean_object* v___y_328_){
_start:
{
uint8_t v_isExporting_boxed_329_; lean_object* v_res_330_; 
v_isExporting_boxed_329_ = lean_unbox(v_isExporting_323_);
v_res_330_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_322_, v_isExporting_boxed_329_, v___x_324_, v___y_325_, v___x_326_, v_a_x3f_327_);
lean_dec(v_a_x3f_327_);
lean_dec(v___y_325_);
lean_dec(v___y_322_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_331_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_336_);
lean_ctor_set(v___x_337_, 5, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_338_, uint8_t v_isExporting_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_env_346_; uint8_t v_isExporting_347_; lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v_nextMacroScope_350_; lean_object* v_ngen_351_; lean_object* v_auxDeclNGen_352_; lean_object* v_traceState_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_410_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v_isExporting_347_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*8);
lean_dec_ref(v_env_346_);
v___x_348_ = lean_st_ref_take(v___y_343_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_350_ = lean_ctor_get(v___x_348_, 1);
v_ngen_351_ = lean_ctor_get(v___x_348_, 2);
v_auxDeclNGen_352_ = lean_ctor_get(v___x_348_, 3);
v_traceState_353_ = lean_ctor_get(v___x_348_, 4);
v_messages_354_ = lean_ctor_get(v___x_348_, 6);
v_infoState_355_ = lean_ctor_get(v___x_348_, 7);
v_snapshotTasks_356_ = lean_ctor_get(v___x_348_, 8);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_348_, 5);
lean_dec(v_unused_411_);
v___x_358_ = v___x_348_;
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_traceState_353_);
lean_inc(v_auxDeclNGen_352_);
lean_inc(v_ngen_351_);
lean_inc(v_nextMacroScope_350_);
lean_inc(v_env_349_);
lean_dec(v___x_348_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = l_Lean_Environment_setExporting(v_env_349_, v_isExporting_339_);
v___x_361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 5, v___x_361_);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_nextMacroScope_350_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_ngen_351_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_auxDeclNGen_352_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_traceState_353_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_snapshotTasks_356_);
v___x_363_ = v_reuseFailAlloc_409_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v_zetaDeltaFVarIds_367_; lean_object* v_postponed_368_; lean_object* v_diag_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_407_; 
v___x_364_ = lean_st_ref_set(v___y_343_, v___x_363_);
v___x_365_ = lean_st_ref_take(v___y_341_);
v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
v_zetaDeltaFVarIds_367_ = lean_ctor_get(v___x_365_, 2);
v_postponed_368_ = lean_ctor_get(v___x_365_, 3);
v_diag_369_ = lean_ctor_get(v___x_365_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_365_, 1);
lean_dec(v_unused_408_);
v___x_371_ = v___x_365_;
v_isShared_372_ = v_isSharedCheck_407_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_diag_369_);
lean_inc(v_postponed_368_);
lean_inc(v_zetaDeltaFVarIds_367_);
lean_inc(v_mctx_366_);
lean_dec(v___x_365_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_407_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_mctx_366_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_367_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_368_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_369_);
v___x_375_ = v_reuseFailAlloc_406_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v_r_377_; 
v___x_376_ = lean_st_ref_set(v___y_341_, v___x_375_);
lean_inc(v___y_343_);
lean_inc(v___y_341_);
v_r_377_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_394_; 
v_a_378_ = lean_ctor_get(v_r_377_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_394_ == 0)
{
v___x_380_ = v_r_377_;
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_r_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
lean_inc(v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_393_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v___x_384_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_361_, v___y_341_, v___x_373_, v___x_383_);
lean_dec_ref(v___x_383_);
lean_dec(v___y_341_);
lean_dec(v___y_343_);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_384_, 0);
lean_dec(v_unused_392_);
v___x_386_ = v___x_384_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_dec(v___x_384_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_a_378_);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_378_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_395_ = lean_ctor_get(v_r_377_, 0);
lean_inc(v_a_395_);
lean_dec_ref(v_r_377_);
v___x_396_ = lean_box(0);
v___x_397_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_361_, v___y_341_, v___x_373_, v___x_396_);
lean_dec(v___y_341_);
lean_dec(v___y_343_);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v___x_397_, 0);
lean_dec(v_unused_405_);
v___x_399_ = v___x_397_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_dec(v___x_397_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 1);
lean_ctor_set(v___x_399_, 0, v_a_395_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_395_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_412_, lean_object* v_isExporting_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v_isExporting_boxed_419_; lean_object* v_res_420_; 
v_isExporting_boxed_419_ = lean_unbox(v_isExporting_413_);
v_res_420_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_412_, v_isExporting_boxed_419_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_421_, lean_object* v_x_422_, uint8_t v_isExporting_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_422_, v_isExporting_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v_isExporting_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v_isExporting_boxed_438_; lean_object* v_res_439_; 
v_isExporting_boxed_438_ = lean_unbox(v_isExporting_432_);
v_res_439_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_430_, v_x_431_, v_isExporting_boxed_438_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_16289__overap_448_; lean_object* v___x_449_; 
v___f_447_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_16289__overap_448_ = lean_panic_fn(v___f_447_, v_msg_441_);
v___x_449_ = lean_apply_5(v___x_16289__overap_448_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_457_, lean_object* v_type_458_, lean_object* v_k_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = 0;
v___x_466_ = 0;
v___x_467_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_457_, v___x_465_, v_type_458_, v_k_459_, v___x_466_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_468_, lean_object* v_type_469_, lean_object* v_k_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_468_, v_type_469_, v_k_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_477_, lean_object* v_alts_478_, lean_object* v_j_479_, lean_object* v_zs1_480_, uint8_t v_isZero_481_, uint8_t v___x_482_, uint8_t v___x_483_, lean_object* v_zs2_484_, lean_object* v_x_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_array_get_borrowed(v___x_477_, v_alts_478_, v_j_479_);
v___x_492_ = l_Array_append___redArg(v_zs1_480_, v_zs2_484_);
lean_inc(v___x_491_);
v___x_493_ = l_Lean_mkAppN(v___x_491_, v___x_492_);
lean_dec_ref(v___x_492_);
v___x_494_ = l_Lean_Meta_mkLambdaFVars(v_zs2_484_, v___x_493_, v_isZero_481_, v___x_482_, v_isZero_481_, v___x_482_, v___x_483_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_495_, lean_object* v_alts_496_, lean_object* v_j_497_, lean_object* v_zs1_498_, lean_object* v_isZero_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v_zs2_502_, lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_isZero_boxed_509_; uint8_t v___x_21408__boxed_510_; uint8_t v___x_21409__boxed_511_; lean_object* v_res_512_; 
v_isZero_boxed_509_ = lean_unbox(v_isZero_499_);
v___x_21408__boxed_510_ = lean_unbox(v___x_500_);
v___x_21409__boxed_511_ = lean_unbox(v___x_501_);
v_res_512_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_495_, v_alts_496_, v_j_497_, v_zs1_498_, v_isZero_boxed_509_, v___x_21408__boxed_510_, v___x_21409__boxed_511_, v_zs2_502_, v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_x_503_);
lean_dec_ref(v_zs2_502_);
lean_dec(v_j_497_);
lean_dec_ref(v_alts_496_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_513_, lean_object* v_ism2_514_, lean_object* v_motive_515_, uint8_t v_isZero_516_, uint8_t v___x_517_, uint8_t v___x_518_, lean_object* v_a_519_, lean_object* v___f_520_, lean_object* v_zs1_521_, lean_object* v_val_522_, lean_object* v___x_523_, lean_object* v_indName_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_params_527_, lean_object* v___x_528_, lean_object* v_h_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = l_Array_append___redArg(v___x_513_, v_ism2_514_);
v___x_536_ = l_Lean_mkAppN(v_motive_515_, v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = l_Lean_Meta_mkLambdaFVars(v_ism2_514_, v___x_536_, v_isZero_516_, v___x_517_, v_isZero_516_, v___x_517_, v___x_518_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref(v___x_537_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
v___x_539_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_519_, v___f_520_, v_isZero_516_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___y_542_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
v___x_545_ = l_Lean_InductiveVal_numCtors(v_val_522_);
v___x_546_ = lean_nat_dec_eq(v___x_545_, v___x_523_);
lean_dec(v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___x_528_);
v___x_547_ = l_Lean_mkConstructorElimName(v_indName_524_, v___x_525_);
v___x_548_ = l_Lean_mkConst(v___x_547_, v___x_526_);
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_523_);
v___x_550_ = lean_array_push(v___x_549_, v_a_538_);
v___x_551_ = l_Array_append___redArg(v_params_527_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_Array_append___redArg(v___x_551_, v_ism2_514_);
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = lean_mk_empty_array_with_capacity(v___x_553_);
lean_inc_ref(v_h_529_);
v___x_555_ = lean_array_push(v___x_554_, v_h_529_);
v___x_556_ = lean_array_push(v___x_555_, v_a_540_);
v___x_557_ = l_Array_append___redArg(v___x_552_, v___x_556_);
lean_dec_ref(v___x_556_);
v___x_558_ = l_Lean_mkAppN(v___x_548_, v___x_557_);
lean_dec_ref(v___x_557_);
v___y_542_ = v___x_558_;
goto v___jp_541_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_525_);
lean_dec(v_indName_524_);
v___x_559_ = l_Lean_mkConst(v___x_528_, v___x_526_);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_523_);
lean_inc_ref(v___x_560_);
v___x_561_ = lean_array_push(v___x_560_, v_a_538_);
v___x_562_ = l_Array_append___redArg(v_params_527_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_563_ = l_Array_append___redArg(v___x_562_, v_ism2_514_);
v___x_564_ = lean_array_push(v___x_560_, v_a_540_);
v___x_565_ = l_Array_append___redArg(v___x_563_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_Lean_mkAppN(v___x_559_, v___x_565_);
lean_dec_ref(v___x_565_);
v___y_542_ = v___x_566_;
goto v___jp_541_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_array_push(v_zs1_521_, v_h_529_);
v___x_544_ = l_Lean_Meta_mkLambdaFVars(v___x_543_, v___y_542_, v_isZero_516_, v___x_517_, v_isZero_516_, v___x_517_, v___x_518_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___x_543_);
return v___x_544_;
}
}
else
{
lean_dec(v_a_538_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_h_529_);
lean_dec(v___x_528_);
lean_dec_ref(v_params_527_);
lean_dec(v___x_526_);
lean_dec(v___x_525_);
lean_dec(v_indName_524_);
lean_dec_ref(v_zs1_521_);
return v___x_539_;
}
}
else
{
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_h_529_);
lean_dec(v___x_528_);
lean_dec_ref(v_params_527_);
lean_dec(v___x_526_);
lean_dec(v___x_525_);
lean_dec(v_indName_524_);
lean_dec_ref(v_zs1_521_);
lean_dec_ref(v___f_520_);
lean_dec_ref(v_a_519_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_567_ = _args[0];
lean_object* v_ism2_568_ = _args[1];
lean_object* v_motive_569_ = _args[2];
lean_object* v_isZero_570_ = _args[3];
lean_object* v___x_571_ = _args[4];
lean_object* v___x_572_ = _args[5];
lean_object* v_a_573_ = _args[6];
lean_object* v___f_574_ = _args[7];
lean_object* v_zs1_575_ = _args[8];
lean_object* v_val_576_ = _args[9];
lean_object* v___x_577_ = _args[10];
lean_object* v_indName_578_ = _args[11];
lean_object* v___x_579_ = _args[12];
lean_object* v___x_580_ = _args[13];
lean_object* v_params_581_ = _args[14];
lean_object* v___x_582_ = _args[15];
lean_object* v_h_583_ = _args[16];
lean_object* v___y_584_ = _args[17];
lean_object* v___y_585_ = _args[18];
lean_object* v___y_586_ = _args[19];
lean_object* v___y_587_ = _args[20];
lean_object* v___y_588_ = _args[21];
_start:
{
uint8_t v_isZero_boxed_589_; uint8_t v___x_21443__boxed_590_; uint8_t v___x_21444__boxed_591_; lean_object* v_res_592_; 
v_isZero_boxed_589_ = lean_unbox(v_isZero_570_);
v___x_21443__boxed_590_ = lean_unbox(v___x_571_);
v___x_21444__boxed_591_ = lean_unbox(v___x_572_);
v_res_592_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_567_, v_ism2_568_, v_motive_569_, v_isZero_boxed_589_, v___x_21443__boxed_590_, v___x_21444__boxed_591_, v_a_573_, v___f_574_, v_zs1_575_, v_val_576_, v___x_577_, v_indName_578_, v___x_579_, v___x_580_, v_params_581_, v___x_582_, v_h_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___x_577_);
lean_dec_ref(v_val_576_);
lean_dec_ref(v_ism2_568_);
return v_res_592_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_593_; lean_object* v_dummy_594_; 
v___x_593_ = lean_box(0);
v_dummy_594_ = l_Lean_Expr_sort___override(v___x_593_);
return v_dummy_594_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_603_ = l_Lean_mkConst(v___x_602_, v___x_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_604_, lean_object* v_alts_605_, lean_object* v_j_606_, uint8_t v_isZero_607_, uint8_t v___x_608_, uint8_t v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_ism2_613_, lean_object* v_motive_614_, lean_object* v_a_615_, lean_object* v_val_616_, lean_object* v_indName_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v_params_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_zs1_624_, lean_object* v_ctorRet1_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
v___x_631_ = lean_whnf(v_ctorRet1_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v_dummy_638_; lean_object* v_nargs_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = lean_box(v_isZero_607_);
v___x_634_ = lean_box(v___x_608_);
v___x_635_ = lean_box(v___x_609_);
lean_inc_ref(v_zs1_624_);
lean_inc(v_j_606_);
v___f_636_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_636_, 0, v___x_604_);
lean_closure_set(v___f_636_, 1, v_alts_605_);
lean_closure_set(v___f_636_, 2, v_j_606_);
lean_closure_set(v___f_636_, 3, v_zs1_624_);
lean_closure_set(v___f_636_, 4, v___x_633_);
lean_closure_set(v___f_636_, 5, v___x_634_);
lean_closure_set(v___f_636_, 6, v___x_635_);
v___x_637_ = l_Lean_mkAppN(v___x_610_, v_zs1_624_);
v_dummy_638_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_639_ = l_Lean_Expr_getAppNumArgs(v_a_632_);
lean_inc(v_nargs_639_);
v___x_640_ = lean_mk_array(v_nargs_639_, v_dummy_638_);
v___x_641_ = lean_nat_sub(v_nargs_639_, v___x_611_);
lean_dec(v_nargs_639_);
v___x_642_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_632_, v___x_640_, v___x_641_);
v___x_643_ = lean_array_get_size(v___x_642_);
v___x_644_ = l_Array_toSubarray___redArg(v___x_642_, v___x_612_, v___x_643_);
v___x_645_ = l_Subarray_copy___redArg(v___x_644_);
v___x_646_ = lean_array_push(v___x_645_, v___x_637_);
v___x_647_ = lean_box(v_isZero_607_);
v___x_648_ = lean_box(v___x_608_);
v___x_649_ = lean_box(v___x_609_);
lean_inc(v___x_611_);
v___f_650_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_650_, 0, v___x_646_);
lean_closure_set(v___f_650_, 1, v_ism2_613_);
lean_closure_set(v___f_650_, 2, v_motive_614_);
lean_closure_set(v___f_650_, 3, v___x_647_);
lean_closure_set(v___f_650_, 4, v___x_648_);
lean_closure_set(v___f_650_, 5, v___x_649_);
lean_closure_set(v___f_650_, 6, v_a_615_);
lean_closure_set(v___f_650_, 7, v___f_636_);
lean_closure_set(v___f_650_, 8, v_zs1_624_);
lean_closure_set(v___f_650_, 9, v_val_616_);
lean_closure_set(v___f_650_, 10, v___x_611_);
lean_closure_set(v___f_650_, 11, v_indName_617_);
lean_closure_set(v___f_650_, 12, v___x_618_);
lean_closure_set(v___f_650_, 13, v___x_619_);
lean_closure_set(v___f_650_, 14, v_params_620_);
lean_closure_set(v___f_650_, 15, v___x_621_);
v___x_651_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_652_ = l_Lean_Level_ofNat(v___x_611_);
lean_dec(v___x_611_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_mkConst(v___x_651_, v___x_654_);
v___x_656_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_657_ = l_Lean_mkRawNatLit(v_j_606_);
v___x_658_ = l_Lean_mkApp3(v___x_655_, v___x_656_, v___x_622_, v___x_657_);
v___x_659_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_623_, v___x_658_, v___f_650_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_659_;
}
else
{
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v_zs1_624_);
lean_dec(v___x_623_);
lean_dec_ref(v___x_622_);
lean_dec(v___x_621_);
lean_dec_ref(v_params_620_);
lean_dec(v___x_619_);
lean_dec(v___x_618_);
lean_dec(v_indName_617_);
lean_dec_ref(v_val_616_);
lean_dec_ref(v_a_615_);
lean_dec_ref(v_motive_614_);
lean_dec_ref(v_ism2_613_);
lean_dec(v___x_612_);
lean_dec(v___x_611_);
lean_dec_ref(v___x_610_);
lean_dec(v_j_606_);
lean_dec_ref(v_alts_605_);
lean_dec_ref(v___x_604_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_660_ = _args[0];
lean_object* v_alts_661_ = _args[1];
lean_object* v_j_662_ = _args[2];
lean_object* v_isZero_663_ = _args[3];
lean_object* v___x_664_ = _args[4];
lean_object* v___x_665_ = _args[5];
lean_object* v___x_666_ = _args[6];
lean_object* v___x_667_ = _args[7];
lean_object* v___x_668_ = _args[8];
lean_object* v_ism2_669_ = _args[9];
lean_object* v_motive_670_ = _args[10];
lean_object* v_a_671_ = _args[11];
lean_object* v_val_672_ = _args[12];
lean_object* v_indName_673_ = _args[13];
lean_object* v___x_674_ = _args[14];
lean_object* v___x_675_ = _args[15];
lean_object* v_params_676_ = _args[16];
lean_object* v___x_677_ = _args[17];
lean_object* v___x_678_ = _args[18];
lean_object* v___x_679_ = _args[19];
lean_object* v_zs1_680_ = _args[20];
lean_object* v_ctorRet1_681_ = _args[21];
lean_object* v___y_682_ = _args[22];
lean_object* v___y_683_ = _args[23];
lean_object* v___y_684_ = _args[24];
lean_object* v___y_685_ = _args[25];
lean_object* v___y_686_ = _args[26];
_start:
{
uint8_t v_isZero_boxed_687_; uint8_t v___x_21574__boxed_688_; uint8_t v___x_21575__boxed_689_; lean_object* v_res_690_; 
v_isZero_boxed_687_ = lean_unbox(v_isZero_663_);
v___x_21574__boxed_688_ = lean_unbox(v___x_664_);
v___x_21575__boxed_689_ = lean_unbox(v___x_665_);
v_res_690_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_660_, v_alts_661_, v_j_662_, v_isZero_boxed_687_, v___x_21574__boxed_688_, v___x_21575__boxed_689_, v___x_666_, v___x_667_, v___x_668_, v_ism2_669_, v_motive_670_, v_a_671_, v_val_672_, v_indName_673_, v___x_674_, v___x_675_, v_params_676_, v___x_677_, v___x_678_, v___x_679_, v_zs1_680_, v_ctorRet1_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_694_, lean_object* v_params_695_, lean_object* v_alts_696_, lean_object* v___x_697_, lean_object* v_ism2_698_, lean_object* v_motive_699_, lean_object* v_val_700_, lean_object* v_indName_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v_as_705_, lean_object* v_i_706_, lean_object* v_j_707_, lean_object* v_bs_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_zero_714_; uint8_t v_isZero_715_; 
v_zero_714_ = lean_unsigned_to_nat(0u);
v_isZero_715_ = lean_nat_dec_eq(v_i_706_, v_zero_714_);
if (v_isZero_715_ == 1)
{
lean_object* v___x_716_; 
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v_j_707_);
lean_dec(v_i_706_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
lean_dec(v_indName_701_);
lean_dec_ref(v_val_700_);
lean_dec_ref(v_motive_699_);
lean_dec_ref(v_ism2_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_alts_696_);
lean_dec_ref(v_params_695_);
lean_dec(v_tail_694_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_bs_708_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v_n_718_; lean_object* v___y_720_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v_n_718_ = lean_nat_sub(v_i_706_, v___x_717_);
lean_dec(v_i_706_);
v___x_733_ = lean_array_fget_borrowed(v_as_705_, v_j_707_);
lean_inc(v_tail_694_);
lean_inc(v___x_733_);
v___x_734_ = l_Lean_mkConst(v___x_733_, v_tail_694_);
v___x_735_ = l_Lean_mkAppN(v___x_734_, v_params_695_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc_ref(v___x_735_);
v___x_736_ = lean_infer_type(v___x_735_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; uint8_t v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_instInhabitedExpr;
v___x_739_ = 1;
v___x_740_ = 1;
v___x_741_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_742_ = lean_box(v_isZero_715_);
v___x_743_ = lean_box(v___x_739_);
v___x_744_ = lean_box(v___x_740_);
lean_inc_ref(v___x_704_);
lean_inc(v___x_703_);
lean_inc_ref(v_params_695_);
lean_inc(v___x_702_);
lean_inc(v___x_733_);
lean_inc(v_indName_701_);
lean_inc_ref(v_val_700_);
lean_inc(v_a_737_);
lean_inc_ref(v_motive_699_);
lean_inc_ref(v_ism2_698_);
lean_inc(v___x_697_);
lean_inc(v_j_707_);
lean_inc_ref(v_alts_696_);
v___f_745_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_745_, 0, v___x_738_);
lean_closure_set(v___f_745_, 1, v_alts_696_);
lean_closure_set(v___f_745_, 2, v_j_707_);
lean_closure_set(v___f_745_, 3, v___x_742_);
lean_closure_set(v___f_745_, 4, v___x_743_);
lean_closure_set(v___f_745_, 5, v___x_744_);
lean_closure_set(v___f_745_, 6, v___x_735_);
lean_closure_set(v___f_745_, 7, v___x_717_);
lean_closure_set(v___f_745_, 8, v___x_697_);
lean_closure_set(v___f_745_, 9, v_ism2_698_);
lean_closure_set(v___f_745_, 10, v_motive_699_);
lean_closure_set(v___f_745_, 11, v_a_737_);
lean_closure_set(v___f_745_, 12, v_val_700_);
lean_closure_set(v___f_745_, 13, v_indName_701_);
lean_closure_set(v___f_745_, 14, v___x_733_);
lean_closure_set(v___f_745_, 15, v___x_702_);
lean_closure_set(v___f_745_, 16, v_params_695_);
lean_closure_set(v___f_745_, 17, v___x_703_);
lean_closure_set(v___f_745_, 18, v___x_704_);
lean_closure_set(v___f_745_, 19, v___x_741_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
v___x_746_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_737_, v___f_745_, v_isZero_715_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v___y_720_ = v___x_746_;
goto v___jp_719_;
}
else
{
lean_dec_ref(v___x_735_);
v___y_720_ = v___x_736_;
goto v___jp_719_;
}
v___jp_719_:
{
if (lean_obj_tag(v___y_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___y_720_);
v___x_722_ = lean_nat_add(v_j_707_, v___x_717_);
lean_dec(v_j_707_);
v___x_723_ = lean_array_push(v_bs_708_, v_a_721_);
v_i_706_ = v_n_718_;
v_j_707_ = v___x_722_;
v_bs_708_ = v___x_723_;
goto _start;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_n_718_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v_bs_708_);
lean_dec(v_j_707_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
lean_dec(v_indName_701_);
lean_dec_ref(v_val_700_);
lean_dec_ref(v_motive_699_);
lean_dec_ref(v_ism2_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_alts_696_);
lean_dec_ref(v_params_695_);
lean_dec(v_tail_694_);
v_a_725_ = lean_ctor_get(v___y_720_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___y_720_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___y_720_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___y_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_747_ = _args[0];
lean_object* v_params_748_ = _args[1];
lean_object* v_alts_749_ = _args[2];
lean_object* v___x_750_ = _args[3];
lean_object* v_ism2_751_ = _args[4];
lean_object* v_motive_752_ = _args[5];
lean_object* v_val_753_ = _args[6];
lean_object* v_indName_754_ = _args[7];
lean_object* v___x_755_ = _args[8];
lean_object* v___x_756_ = _args[9];
lean_object* v___x_757_ = _args[10];
lean_object* v_as_758_ = _args[11];
lean_object* v_i_759_ = _args[12];
lean_object* v_j_760_ = _args[13];
lean_object* v_bs_761_ = _args[14];
lean_object* v___y_762_ = _args[15];
lean_object* v___y_763_ = _args[16];
lean_object* v___y_764_ = _args[17];
lean_object* v___y_765_ = _args[18];
lean_object* v___y_766_ = _args[19];
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_747_, v_params_748_, v_alts_749_, v___x_750_, v_ism2_751_, v_motive_752_, v_val_753_, v_indName_754_, v___x_755_, v___x_756_, v___x_757_, v_as_758_, v_i_759_, v_j_760_, v_bs_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec_ref(v_as_758_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_768_, lean_object* v___x_769_, lean_object* v_a_770_, lean_object* v_ism1_771_, uint8_t v___x_772_, uint8_t v___x_773_, uint8_t v___x_774_, lean_object* v___x_775_, lean_object* v_tail_776_, lean_object* v_params_777_, lean_object* v_alts_778_, lean_object* v_numParams_779_, lean_object* v_ism2_780_, lean_object* v_val_781_, lean_object* v_indName_782_, lean_object* v___x_783_, lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_name_786_, lean_object* v___x_787_, lean_object* v_heq_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc_ref(v_motive_768_);
v___x_794_ = l_Lean_mkAppN(v_motive_768_, v___x_769_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
v___x_795_ = l_Lean_mkArrow(v_a_770_, v___x_794_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
v___x_797_ = l_Lean_Meta_mkLambdaFVars(v_ism1_771_, v_a_796_, v___x_772_, v___x_773_, v___x_772_, v___x_773_, v___x_774_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = lean_array_get_size(v___x_775_);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_799_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___x_783_);
lean_inc_ref(v_motive_768_);
lean_inc_ref(v_ism2_780_);
lean_inc_ref(v_alts_778_);
lean_inc_ref(v_params_777_);
v___x_802_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_776_, v_params_777_, v_alts_778_, v_numParams_779_, v_ism2_780_, v_motive_768_, v_val_781_, v_indName_782_, v___x_783_, v___x_784_, v___x_785_, v___x_775_, v___x_799_, v___x_800_, v___x_801_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc_ref(v_heq_788_);
v___x_804_ = l_Lean_Meta_mkEqSymm(v_heq_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_804_);
v___x_806_ = l_Lean_mkConst(v_name_786_, v___x_783_);
v___x_807_ = l_Lean_mkAppN(v___x_806_, v_params_777_);
v___x_808_ = l_Lean_Expr_app___override(v___x_807_, v_a_798_);
v___x_809_ = l_Lean_mkAppN(v___x_808_, v_ism1_771_);
v___x_810_ = l_Lean_mkAppN(v___x_809_, v_a_803_);
lean_dec(v_a_803_);
v___x_811_ = l_Lean_Expr_app___override(v___x_810_, v_a_805_);
v___x_812_ = lean_mk_empty_array_with_capacity(v___x_787_);
lean_inc_ref(v___x_812_);
v___x_813_ = lean_array_push(v___x_812_, v_motive_768_);
v___x_814_ = l_Array_append___redArg(v_params_777_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Array_append___redArg(v___x_814_, v_ism1_771_);
v___x_816_ = l_Array_append___redArg(v___x_815_, v_ism2_780_);
lean_dec_ref(v_ism2_780_);
v___x_817_ = lean_array_push(v___x_812_, v_heq_788_);
v___x_818_ = l_Array_append___redArg(v___x_816_, v___x_817_);
lean_dec_ref(v___x_817_);
v___x_819_ = l_Array_append___redArg(v___x_818_, v_alts_778_);
lean_dec_ref(v_alts_778_);
v___x_820_ = l_Lean_Meta_mkLambdaFVars(v___x_819_, v___x_811_, v___x_772_, v___x_773_, v___x_772_, v___x_773_, v___x_774_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v___x_819_);
return v___x_820_;
}
else
{
lean_dec(v_a_803_);
lean_dec(v_a_798_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec(v___x_783_);
lean_dec_ref(v_ism2_780_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec_ref(v_motive_768_);
return v___x_804_;
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_798_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec(v___x_783_);
lean_dec_ref(v_ism2_780_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec_ref(v_motive_768_);
v_a_821_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_802_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_802_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec_ref(v___x_785_);
lean_dec(v___x_784_);
lean_dec(v___x_783_);
lean_dec(v_indName_782_);
lean_dec_ref(v_val_781_);
lean_dec_ref(v_ism2_780_);
lean_dec(v_numParams_779_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec(v_tail_776_);
lean_dec_ref(v_motive_768_);
return v___x_797_;
}
}
else
{
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec_ref(v___x_785_);
lean_dec(v___x_784_);
lean_dec(v___x_783_);
lean_dec(v_indName_782_);
lean_dec_ref(v_val_781_);
lean_dec_ref(v_ism2_780_);
lean_dec(v_numParams_779_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec(v_tail_776_);
lean_dec_ref(v_motive_768_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_829_ = _args[0];
lean_object* v___x_830_ = _args[1];
lean_object* v_a_831_ = _args[2];
lean_object* v_ism1_832_ = _args[3];
lean_object* v___x_833_ = _args[4];
lean_object* v___x_834_ = _args[5];
lean_object* v___x_835_ = _args[6];
lean_object* v___x_836_ = _args[7];
lean_object* v_tail_837_ = _args[8];
lean_object* v_params_838_ = _args[9];
lean_object* v_alts_839_ = _args[10];
lean_object* v_numParams_840_ = _args[11];
lean_object* v_ism2_841_ = _args[12];
lean_object* v_val_842_ = _args[13];
lean_object* v_indName_843_ = _args[14];
lean_object* v___x_844_ = _args[15];
lean_object* v___x_845_ = _args[16];
lean_object* v___x_846_ = _args[17];
lean_object* v_name_847_ = _args[18];
lean_object* v___x_848_ = _args[19];
lean_object* v_heq_849_ = _args[20];
lean_object* v___y_850_ = _args[21];
lean_object* v___y_851_ = _args[22];
lean_object* v___y_852_ = _args[23];
lean_object* v___y_853_ = _args[24];
lean_object* v___y_854_ = _args[25];
_start:
{
uint8_t v___x_21799__boxed_855_; uint8_t v___x_21800__boxed_856_; uint8_t v___x_21801__boxed_857_; lean_object* v_res_858_; 
v___x_21799__boxed_855_ = lean_unbox(v___x_833_);
v___x_21800__boxed_856_ = lean_unbox(v___x_834_);
v___x_21801__boxed_857_ = lean_unbox(v___x_835_);
v_res_858_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_829_, v___x_830_, v_a_831_, v_ism1_832_, v___x_21799__boxed_855_, v___x_21800__boxed_856_, v___x_21801__boxed_857_, v___x_836_, v_tail_837_, v_params_838_, v_alts_839_, v_numParams_840_, v_ism2_841_, v_val_842_, v_indName_843_, v___x_844_, v___x_845_, v___x_846_, v_name_847_, v___x_848_, v_heq_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_836_);
lean_dec_ref(v_ism1_832_);
lean_dec_ref(v___x_830_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_859_, lean_object* v_tail_860_, lean_object* v_params_861_, lean_object* v_ism1_862_, lean_object* v_ism2_863_, lean_object* v_motive_864_, lean_object* v___x_865_, uint8_t v___x_866_, uint8_t v___x_867_, uint8_t v___x_868_, lean_object* v___x_869_, lean_object* v_numParams_870_, lean_object* v_val_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_name_874_, lean_object* v___x_875_, lean_object* v_alts_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_inc(v_indName_859_);
v___x_882_ = l_mkCtorIdxName(v_indName_859_);
lean_inc(v_tail_860_);
v___x_883_ = l_Lean_mkConst(v___x_882_, v_tail_860_);
lean_inc_ref(v_params_861_);
v___x_884_ = l_Array_append___redArg(v_params_861_, v_ism1_862_);
lean_inc_ref(v___x_883_);
v___x_885_ = l_Lean_mkAppN(v___x_883_, v___x_884_);
lean_dec_ref(v___x_884_);
lean_inc_ref(v_params_861_);
v___x_886_ = l_Array_append___redArg(v_params_861_, v_ism2_863_);
v___x_887_ = l_Lean_mkAppN(v___x_883_, v___x_886_);
lean_dec_ref(v___x_886_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc_ref(v___x_887_);
lean_inc_ref(v___x_885_);
v___x_888_ = l_Lean_Meta_mkEq(v___x_885_, v___x_887_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc_ref(v___x_887_);
v___x_890_ = l_Lean_Meta_mkEq(v___x_887_, v___x_885_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = lean_box(v___x_866_);
v___x_893_ = lean_box(v___x_867_);
v___x_894_ = lean_box(v___x_868_);
v___f_895_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_895_, 0, v_motive_864_);
lean_closure_set(v___f_895_, 1, v___x_865_);
lean_closure_set(v___f_895_, 2, v_a_891_);
lean_closure_set(v___f_895_, 3, v_ism1_862_);
lean_closure_set(v___f_895_, 4, v___x_892_);
lean_closure_set(v___f_895_, 5, v___x_893_);
lean_closure_set(v___f_895_, 6, v___x_894_);
lean_closure_set(v___f_895_, 7, v___x_869_);
lean_closure_set(v___f_895_, 8, v_tail_860_);
lean_closure_set(v___f_895_, 9, v_params_861_);
lean_closure_set(v___f_895_, 10, v_alts_876_);
lean_closure_set(v___f_895_, 11, v_numParams_870_);
lean_closure_set(v___f_895_, 12, v_ism2_863_);
lean_closure_set(v___f_895_, 13, v_val_871_);
lean_closure_set(v___f_895_, 14, v_indName_859_);
lean_closure_set(v___f_895_, 15, v___x_872_);
lean_closure_set(v___f_895_, 16, v___x_873_);
lean_closure_set(v___f_895_, 17, v___x_887_);
lean_closure_set(v___f_895_, 18, v_name_874_);
lean_closure_set(v___f_895_, 19, v___x_875_);
v___x_896_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_897_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_896_, v_a_889_, v___f_895_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_897_;
}
else
{
lean_dec(v_a_889_);
lean_dec_ref(v___x_887_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v_alts_876_);
lean_dec(v___x_875_);
lean_dec(v_name_874_);
lean_dec(v___x_873_);
lean_dec(v___x_872_);
lean_dec_ref(v_val_871_);
lean_dec(v_numParams_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v_motive_864_);
lean_dec_ref(v_ism2_863_);
lean_dec_ref(v_ism1_862_);
lean_dec_ref(v_params_861_);
lean_dec(v_tail_860_);
lean_dec(v_indName_859_);
return v___x_890_;
}
}
else
{
lean_dec_ref(v___x_887_);
lean_dec_ref(v___x_885_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v_alts_876_);
lean_dec(v___x_875_);
lean_dec(v_name_874_);
lean_dec(v___x_873_);
lean_dec(v___x_872_);
lean_dec_ref(v_val_871_);
lean_dec(v_numParams_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v_motive_864_);
lean_dec_ref(v_ism2_863_);
lean_dec_ref(v_ism1_862_);
lean_dec_ref(v_params_861_);
lean_dec(v_tail_860_);
lean_dec(v_indName_859_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_898_ = _args[0];
lean_object* v_tail_899_ = _args[1];
lean_object* v_params_900_ = _args[2];
lean_object* v_ism1_901_ = _args[3];
lean_object* v_ism2_902_ = _args[4];
lean_object* v_motive_903_ = _args[5];
lean_object* v___x_904_ = _args[6];
lean_object* v___x_905_ = _args[7];
lean_object* v___x_906_ = _args[8];
lean_object* v___x_907_ = _args[9];
lean_object* v___x_908_ = _args[10];
lean_object* v_numParams_909_ = _args[11];
lean_object* v_val_910_ = _args[12];
lean_object* v___x_911_ = _args[13];
lean_object* v___x_912_ = _args[14];
lean_object* v_name_913_ = _args[15];
lean_object* v___x_914_ = _args[16];
lean_object* v_alts_915_ = _args[17];
lean_object* v___y_916_ = _args[18];
lean_object* v___y_917_ = _args[19];
lean_object* v___y_918_ = _args[20];
lean_object* v___y_919_ = _args[21];
lean_object* v___y_920_ = _args[22];
_start:
{
uint8_t v___x_21926__boxed_921_; uint8_t v___x_21927__boxed_922_; uint8_t v___x_21928__boxed_923_; lean_object* v_res_924_; 
v___x_21926__boxed_921_ = lean_unbox(v___x_905_);
v___x_21927__boxed_922_ = lean_unbox(v___x_906_);
v___x_21928__boxed_923_ = lean_unbox(v___x_907_);
v_res_924_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_898_, v_tail_899_, v_params_900_, v_ism1_901_, v_ism2_902_, v_motive_903_, v___x_904_, v___x_21926__boxed_921_, v___x_21927__boxed_922_, v___x_21928__boxed_923_, v___x_908_, v_numParams_909_, v_val_910_, v___x_911_, v___x_912_, v_name_913_, v___x_914_, v_alts_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_926_, lean_object* v_dummy_927_, lean_object* v___x_928_, lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_motive_931_, lean_object* v_zs1_932_, uint8_t v_isZero_933_, uint8_t v___x_934_, uint8_t v___x_935_, lean_object* v___x_936_, lean_object* v_j_937_, lean_object* v_zs2_938_, lean_object* v_ctorRet2_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
v___x_945_ = lean_whnf(v_ctorRet2_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v_nargs_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = l_Lean_mkAppN(v___x_926_, v_zs2_938_);
v_nargs_948_ = l_Lean_Expr_getAppNumArgs(v_a_946_);
lean_inc(v_nargs_948_);
v___x_949_ = lean_mk_array(v_nargs_948_, v_dummy_927_);
v___x_950_ = lean_nat_sub(v_nargs_948_, v___x_928_);
lean_dec(v_nargs_948_);
v___x_951_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_946_, v___x_949_, v___x_950_);
v___x_952_ = lean_array_get_size(v___x_951_);
v___x_953_ = l_Array_toSubarray___redArg(v___x_951_, v___x_929_, v___x_952_);
v___x_954_ = l_Subarray_copy___redArg(v___x_953_);
v___x_955_ = lean_array_push(v___x_954_, v___x_947_);
v___x_956_ = l_Array_append___redArg(v___x_930_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = l_Lean_mkAppN(v_motive_931_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_958_ = l_Array_append___redArg(v_zs1_932_, v_zs2_938_);
v___x_959_ = l_Lean_Meta_mkForallFVars(v___x_958_, v___x_957_, v_isZero_933_, v___x_934_, v___x_934_, v___x_935_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_979_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_979_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_979_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_979_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___y_965_; 
if (lean_obj_tag(v___x_936_) == 1)
{
lean_object* v_str_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_str_970_ = lean_ctor_get(v___x_936_, 1);
lean_inc_ref(v_str_970_);
lean_dec_ref(v___x_936_);
v___x_971_ = lean_box(0);
v___x_972_ = l_Lean_Name_str___override(v___x_971_, v_str_970_);
v___y_965_ = v___x_972_;
goto v___jp_964_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v___x_936_);
v___x_973_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_974_ = lean_nat_add(v_j_937_, v___x_928_);
v___x_975_ = l_Nat_reprFast(v___x_974_);
v___x_976_ = lean_string_append(v___x_973_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_box(0);
v___x_978_ = l_Lean_Name_str___override(v___x_977_, v___x_976_);
v___y_965_ = v___x_978_;
goto v___jp_964_;
}
v___jp_964_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___y_965_);
lean_ctor_set(v___x_966_, 1, v_a_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_966_);
v___x_968_ = v___x_962_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v___x_936_);
v_a_980_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_959_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_959_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___x_936_);
lean_dec_ref(v_zs1_932_);
lean_dec_ref(v_motive_931_);
lean_dec_ref(v___x_930_);
lean_dec(v___x_929_);
lean_dec_ref(v_dummy_927_);
lean_dec_ref(v___x_926_);
v_a_988_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_945_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_945_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_996_ = _args[0];
lean_object* v_dummy_997_ = _args[1];
lean_object* v___x_998_ = _args[2];
lean_object* v___x_999_ = _args[3];
lean_object* v___x_1000_ = _args[4];
lean_object* v_motive_1001_ = _args[5];
lean_object* v_zs1_1002_ = _args[6];
lean_object* v_isZero_1003_ = _args[7];
lean_object* v___x_1004_ = _args[8];
lean_object* v___x_1005_ = _args[9];
lean_object* v___x_1006_ = _args[10];
lean_object* v_j_1007_ = _args[11];
lean_object* v_zs2_1008_ = _args[12];
lean_object* v_ctorRet2_1009_ = _args[13];
lean_object* v___y_1010_ = _args[14];
lean_object* v___y_1011_ = _args[15];
lean_object* v___y_1012_ = _args[16];
lean_object* v___y_1013_ = _args[17];
lean_object* v___y_1014_ = _args[18];
_start:
{
uint8_t v_isZero_boxed_1015_; uint8_t v___x_22010__boxed_1016_; uint8_t v___x_22011__boxed_1017_; lean_object* v_res_1018_; 
v_isZero_boxed_1015_ = lean_unbox(v_isZero_1003_);
v___x_22010__boxed_1016_ = lean_unbox(v___x_1004_);
v___x_22011__boxed_1017_ = lean_unbox(v___x_1005_);
v_res_1018_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_996_, v_dummy_997_, v___x_998_, v___x_999_, v___x_1000_, v_motive_1001_, v_zs1_1002_, v_isZero_boxed_1015_, v___x_22010__boxed_1016_, v___x_22011__boxed_1017_, v___x_1006_, v_j_1007_, v_zs2_1008_, v_ctorRet2_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec_ref(v_zs2_1008_);
lean_dec(v_j_1007_);
lean_dec(v___x_998_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v_motive_1022_, uint8_t v_isZero_1023_, uint8_t v___x_1024_, uint8_t v___x_1025_, lean_object* v___x_1026_, lean_object* v_j_1027_, lean_object* v_a_1028_, lean_object* v_zs1_1029_, lean_object* v_ctorRet1_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
v___x_1036_ = lean_whnf(v_ctorRet1_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v_dummy_1039_; lean_object* v_nargs_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
lean_inc_ref(v___x_1019_);
v___x_1038_ = l_Lean_mkAppN(v___x_1019_, v_zs1_1029_);
v_dummy_1039_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1040_ = l_Lean_Expr_getAppNumArgs(v_a_1037_);
lean_inc(v_nargs_1040_);
v___x_1041_ = lean_mk_array(v_nargs_1040_, v_dummy_1039_);
v___x_1042_ = lean_nat_sub(v_nargs_1040_, v___x_1020_);
lean_dec(v_nargs_1040_);
v___x_1043_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1037_, v___x_1041_, v___x_1042_);
v___x_1044_ = lean_array_get_size(v___x_1043_);
lean_inc(v___x_1021_);
v___x_1045_ = l_Array_toSubarray___redArg(v___x_1043_, v___x_1021_, v___x_1044_);
v___x_1046_ = l_Subarray_copy___redArg(v___x_1045_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1038_);
v___x_1048_ = lean_box(v_isZero_1023_);
v___x_1049_ = lean_box(v___x_1024_);
v___x_1050_ = lean_box(v___x_1025_);
v___f_1051_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1051_, 0, v___x_1019_);
lean_closure_set(v___f_1051_, 1, v_dummy_1039_);
lean_closure_set(v___f_1051_, 2, v___x_1020_);
lean_closure_set(v___f_1051_, 3, v___x_1021_);
lean_closure_set(v___f_1051_, 4, v___x_1047_);
lean_closure_set(v___f_1051_, 5, v_motive_1022_);
lean_closure_set(v___f_1051_, 6, v_zs1_1029_);
lean_closure_set(v___f_1051_, 7, v___x_1048_);
lean_closure_set(v___f_1051_, 8, v___x_1049_);
lean_closure_set(v___f_1051_, 9, v___x_1050_);
lean_closure_set(v___f_1051_, 10, v___x_1026_);
lean_closure_set(v___f_1051_, 11, v_j_1027_);
v___x_1052_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1028_, v___f_1051_, v_isZero_1023_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_zs1_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_j_1027_);
lean_dec(v___x_1026_);
lean_dec_ref(v_motive_1022_);
lean_dec(v___x_1021_);
lean_dec(v___x_1020_);
lean_dec_ref(v___x_1019_);
v_a_1053_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1036_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1036_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1061_ = _args[0];
lean_object* v___x_1062_ = _args[1];
lean_object* v___x_1063_ = _args[2];
lean_object* v_motive_1064_ = _args[3];
lean_object* v_isZero_1065_ = _args[4];
lean_object* v___x_1066_ = _args[5];
lean_object* v___x_1067_ = _args[6];
lean_object* v___x_1068_ = _args[7];
lean_object* v_j_1069_ = _args[8];
lean_object* v_a_1070_ = _args[9];
lean_object* v_zs1_1071_ = _args[10];
lean_object* v_ctorRet1_1072_ = _args[11];
lean_object* v___y_1073_ = _args[12];
lean_object* v___y_1074_ = _args[13];
lean_object* v___y_1075_ = _args[14];
lean_object* v___y_1076_ = _args[15];
lean_object* v___y_1077_ = _args[16];
_start:
{
uint8_t v_isZero_boxed_1078_; uint8_t v___x_22148__boxed_1079_; uint8_t v___x_22149__boxed_1080_; lean_object* v_res_1081_; 
v_isZero_boxed_1078_ = lean_unbox(v_isZero_1065_);
v___x_22148__boxed_1079_ = lean_unbox(v___x_1066_);
v___x_22149__boxed_1080_ = lean_unbox(v___x_1067_);
v_res_1081_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1061_, v___x_1062_, v___x_1063_, v_motive_1064_, v_isZero_boxed_1078_, v___x_22148__boxed_1079_, v___x_22149__boxed_1080_, v___x_1068_, v_j_1069_, v_a_1070_, v_zs1_1071_, v_ctorRet1_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1082_, lean_object* v_params_1083_, lean_object* v___x_1084_, lean_object* v_motive_1085_, lean_object* v_as_1086_, lean_object* v_i_1087_, lean_object* v_j_1088_, lean_object* v_bs_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_zero_1095_; uint8_t v_isZero_1096_; 
v_zero_1095_ = lean_unsigned_to_nat(0u);
v_isZero_1096_ = lean_nat_dec_eq(v_i_1087_, v_zero_1095_);
if (v_isZero_1096_ == 1)
{
lean_object* v___x_1097_; 
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v_j_1088_);
lean_dec(v_i_1087_);
lean_dec_ref(v_motive_1085_);
lean_dec(v___x_1084_);
lean_dec(v_tail_1082_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_bs_1089_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = lean_array_fget_borrowed(v_as_1086_, v_j_1088_);
lean_inc(v_tail_1082_);
lean_inc(v___x_1098_);
v___x_1099_ = l_Lean_mkConst(v___x_1098_, v_tail_1082_);
v___x_1100_ = l_Lean_mkAppN(v___x_1099_, v_params_1083_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc_ref(v___x_1100_);
v___x_1101_ = lean_infer_type(v___x_1100_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; uint8_t v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = 1;
v___x_1104_ = 1;
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_box(v_isZero_1096_);
v___x_1107_ = lean_box(v___x_1103_);
v___x_1108_ = lean_box(v___x_1104_);
lean_inc(v_a_1102_);
lean_inc(v_j_1088_);
lean_inc(v___x_1098_);
lean_inc_ref(v_motive_1085_);
lean_inc(v___x_1084_);
v___f_1109_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1109_, 0, v___x_1100_);
lean_closure_set(v___f_1109_, 1, v___x_1105_);
lean_closure_set(v___f_1109_, 2, v___x_1084_);
lean_closure_set(v___f_1109_, 3, v_motive_1085_);
lean_closure_set(v___f_1109_, 4, v___x_1106_);
lean_closure_set(v___f_1109_, 5, v___x_1107_);
lean_closure_set(v___f_1109_, 6, v___x_1108_);
lean_closure_set(v___f_1109_, 7, v___x_1098_);
lean_closure_set(v___f_1109_, 8, v_j_1088_);
lean_closure_set(v___f_1109_, 9, v_a_1102_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
v___x_1110_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1102_, v___f_1109_, v_isZero_1096_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v_n_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v_n_1112_ = lean_nat_sub(v_i_1087_, v___x_1105_);
lean_dec(v_i_1087_);
v___x_1113_ = lean_nat_add(v_j_1088_, v___x_1105_);
lean_dec(v_j_1088_);
v___x_1114_ = lean_array_push(v_bs_1089_, v_a_1111_);
v_i_1087_ = v_n_1112_;
v_j_1088_ = v___x_1113_;
v_bs_1089_ = v___x_1114_;
goto _start;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_bs_1089_);
lean_dec(v_j_1088_);
lean_dec(v_i_1087_);
lean_dec_ref(v_motive_1085_);
lean_dec(v___x_1084_);
lean_dec(v_tail_1082_);
v_a_1116_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1110_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v___x_1100_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_bs_1089_);
lean_dec(v_j_1088_);
lean_dec(v_i_1087_);
lean_dec_ref(v_motive_1085_);
lean_dec(v___x_1084_);
lean_dec(v_tail_1082_);
v_a_1124_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1101_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1101_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1132_, lean_object* v_params_1133_, lean_object* v___x_1134_, lean_object* v_motive_1135_, lean_object* v_as_1136_, lean_object* v_i_1137_, lean_object* v_j_1138_, lean_object* v_bs_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1132_, v_params_1133_, v___x_1134_, v_motive_1135_, v_as_1136_, v_i_1137_, v_j_1138_, v_bs_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec_ref(v_as_1136_);
lean_dec_ref(v_params_1133_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0(lean_object* v___x_1146_, lean_object* v_a_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_20829__overap_1154_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_instInhabitedExpr;
v___x_20829__overap_1154_ = l_instInhabitedOfMonad___redArg(v___x_1146_, v___x_1153_);
v___x_1155_ = lean_apply_5(v___x_20829__overap_1154_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, lean_box(0));
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0___boxed(lean_object* v___x_1156_, lean_object* v_a_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0(v___x_1156_, v_a_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec_ref(v_a_1157_);
return v_res_1163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0);
v___x_1166_ = l_ReaderT_instMonad___redArg(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1___boxed(lean_object* v_acc_1171_, lean_object* v_declInfos_1172_, lean_object* v_k_1173_, lean_object* v_kind_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_kind_boxed_1181_; lean_object* v_res_1182_; 
v_kind_boxed_1181_ = lean_unbox(v_kind_1174_);
v_res_1182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1(v_acc_1171_, v_declInfos_1172_, v_k_1173_, v_kind_boxed_1181_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(lean_object* v_declInfos_1183_, lean_object* v_k_1184_, uint8_t v_kind_1185_, lean_object* v_acc_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_toApplicative_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1280_; 
v___x_1192_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1);
v_toApplicative_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1192_, 1);
lean_dec(v_unused_1281_);
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1280_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_toApplicative_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1280_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_toFunctor_1197_; lean_object* v_toSeq_1198_; lean_object* v_toSeqLeft_1199_; lean_object* v_toSeqRight_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1278_; 
v_toFunctor_1197_ = lean_ctor_get(v_toApplicative_1193_, 0);
v_toSeq_1198_ = lean_ctor_get(v_toApplicative_1193_, 2);
v_toSeqLeft_1199_ = lean_ctor_get(v_toApplicative_1193_, 3);
v_toSeqRight_1200_ = lean_ctor_get(v_toApplicative_1193_, 4);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_toApplicative_1193_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_dec(v_unused_1279_);
v___x_1202_ = v_toApplicative_1193_;
v_isShared_1203_ = v_isSharedCheck_1278_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_toSeqRight_1200_);
lean_inc(v_toSeqLeft_1199_);
lean_inc(v_toSeq_1198_);
lean_inc(v_toFunctor_1197_);
lean_dec(v_toApplicative_1193_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1278_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1213_; 
v___f_1204_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2));
v___f_1205_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3));
lean_inc_ref(v_toFunctor_1197_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toFunctor_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toFunctor_1197_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___f_1206_);
lean_ctor_set(v___x_1208_, 1, v___f_1207_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toSeqRight_1200_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toSeqLeft_1199_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1211_, 0, v_toSeq_1198_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 4, v___f_1209_);
lean_ctor_set(v___x_1202_, 3, v___f_1210_);
lean_ctor_set(v___x_1202_, 2, v___f_1211_);
lean_ctor_set(v___x_1202_, 1, v___f_1204_);
lean_ctor_set(v___x_1202_, 0, v___x_1208_);
v___x_1213_ = v___x_1202_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v___f_1211_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v___f_1210_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v___f_1209_);
v___x_1213_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___f_1205_);
lean_ctor_set(v___x_1195_, 0, v___x_1213_);
v___x_1215_ = v___x_1195_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___f_1205_);
v___x_1215_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v_toApplicative_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1274_; 
v___x_1216_ = l_ReaderT_instMonad___redArg(v___x_1215_);
v_toApplicative_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1216_, 1);
lean_dec(v_unused_1275_);
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1274_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_toApplicative_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1274_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_toFunctor_1221_; lean_object* v_toSeq_1222_; lean_object* v_toSeqLeft_1223_; lean_object* v_toSeqRight_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1272_; 
v_toFunctor_1221_ = lean_ctor_get(v_toApplicative_1217_, 0);
v_toSeq_1222_ = lean_ctor_get(v_toApplicative_1217_, 2);
v_toSeqLeft_1223_ = lean_ctor_get(v_toApplicative_1217_, 3);
v_toSeqRight_1224_ = lean_ctor_get(v_toApplicative_1217_, 4);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_toApplicative_1217_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v_toApplicative_1217_, 1);
lean_dec(v_unused_1273_);
v___x_1226_ = v_toApplicative_1217_;
v_isShared_1227_ = v_isSharedCheck_1272_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_toSeqRight_1224_);
lean_inc(v_toSeqLeft_1223_);
lean_inc(v_toSeq_1222_);
lean_inc(v_toFunctor_1221_);
lean_dec(v_toApplicative_1217_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1272_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1237_; 
v___f_1228_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4));
v___f_1229_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5));
lean_inc_ref(v_toFunctor_1221_);
v___f_1230_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1230_, 0, v_toFunctor_1221_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toFunctor_1221_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___f_1230_);
lean_ctor_set(v___x_1232_, 1, v___f_1231_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toSeqRight_1224_);
v___f_1234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1234_, 0, v_toSeqLeft_1223_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toSeq_1222_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v___f_1233_);
lean_ctor_set(v___x_1226_, 3, v___f_1234_);
lean_ctor_set(v___x_1226_, 2, v___f_1235_);
lean_ctor_set(v___x_1226_, 1, v___f_1228_);
lean_ctor_set(v___x_1226_, 0, v___x_1232_);
v___x_1237_ = v___x_1226_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___f_1228_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v___f_1234_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v___f_1233_);
v___x_1237_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___f_1229_);
lean_ctor_set(v___x_1219_, 0, v___x_1237_);
v___x_1239_ = v___x_1219_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___f_1229_);
v___x_1239_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = lean_array_get_size(v_acc_1186_);
v___x_1241_ = lean_array_get_size(v_declInfos_1183_);
v___x_1242_ = lean_nat_dec_lt(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_declInfos_1183_);
v___x_1243_ = lean_apply_6(v_k_1184_, v_acc_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1243_;
}
else
{
lean_object* v___f_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_snd_1252_; lean_object* v_fst_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1256_; 
v___f_1244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1244_, 0, v___x_1239_);
v___x_1245_ = lean_box(0);
v___x_1246_ = 0;
v___f_1247_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1247_, 0, v___f_1244_);
v___x_1248_ = lean_box(v___x_1246_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___f_1247_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1245_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_array_get_borrowed(v___x_1250_, v_declInfos_1183_, v___x_1240_);
v_snd_1252_ = lean_ctor_get(v___x_1251_, 1);
v_fst_1253_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_fst_1253_);
v_fst_1254_ = lean_ctor_get(v_snd_1252_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v_snd_1252_, 1);
lean_inc(v_snd_1255_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc_ref(v_acc_1186_);
v___x_1256_ = lean_apply_6(v_snd_1255_, v_acc_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = lean_box(v_kind_1185_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1259_, 0, v_acc_1186_);
lean_closure_set(v___f_1259_, 1, v_declInfos_1183_);
lean_closure_set(v___f_1259_, 2, v_k_1184_);
lean_closure_set(v___f_1259_, 3, v___x_1258_);
v___x_1260_ = lean_unbox(v_fst_1254_);
lean_dec(v_fst_1254_);
v___x_1261_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1253_, v___x_1260_, v_a_1257_, v___f_1259_, v_kind_1185_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1261_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_fst_1254_);
lean_dec(v_fst_1253_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_acc_1186_);
lean_dec_ref(v_k_1184_);
lean_dec_ref(v_declInfos_1183_);
v_a_1262_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1256_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1256_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1(lean_object* v_acc_1282_, lean_object* v_declInfos_1283_, lean_object* v_k_1284_, uint8_t v_kind_1285_, lean_object* v_x_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_array_push(v_acc_1282_, v_x_1286_);
v___x_1293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_1283_, v_k_1284_, v_kind_1285_, v___x_1292_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___boxed(lean_object* v_declInfos_1294_, lean_object* v_k_1295_, lean_object* v_kind_1296_, lean_object* v_acc_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v_kind_boxed_1303_; lean_object* v_res_1304_; 
v_kind_boxed_1303_ = lean_unbox(v_kind_1296_);
v_res_1304_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_1294_, v_k_1295_, v_kind_boxed_1303_, v_acc_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(lean_object* v_inst_1307_, lean_object* v_declInfos_1308_, lean_object* v_k_1309_, uint8_t v_kind_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0));
v___x_1317_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_1308_, v_k_1309_, v_kind_1310_, v___x_1316_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___boxed(lean_object* v_inst_1318_, lean_object* v_declInfos_1319_, lean_object* v_k_1320_, lean_object* v_kind_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v_kind_boxed_1327_; lean_object* v_res_1328_; 
v_kind_boxed_1327_ = lean_unbox(v_kind_1321_);
v_res_1328_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(v_inst_1318_, v_declInfos_1319_, v_k_1320_, v_kind_boxed_1327_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v_inst_1318_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1329_, size_t v_i_1330_, lean_object* v_bs_1331_){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_usize_dec_lt(v_i_1330_, v_sz_1329_);
if (v___x_1332_ == 0)
{
return v_bs_1331_;
}
else
{
lean_object* v_v_1333_; lean_object* v_fst_1334_; lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1351_; 
v_v_1333_ = lean_array_uget(v_bs_1331_, v_i_1330_);
v_fst_1334_ = lean_ctor_get(v_v_1333_, 0);
v_snd_1335_ = lean_ctor_get(v_v_1333_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_v_1333_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1337_ = v_v_1333_;
v_isShared_1338_ = v_isSharedCheck_1351_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_inc(v_fst_1334_);
lean_dec(v_v_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1351_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v_bs_x27_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v_bs_x27_1340_ = lean_array_uset(v_bs_1331_, v_i_1330_, v___x_1339_);
v___x_1341_ = 0;
v___x_1342_ = lean_box(v___x_1341_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1342_);
v___x_1344_ = v___x_1337_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_snd_1335_);
v___x_1344_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_fst_1334_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1330_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1340_, v_i_1330_, v___x_1345_);
v_i_1330_ = v___x_1347_;
v_bs_1331_ = v___x_1348_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1352_, lean_object* v_i_1353_, lean_object* v_bs_1354_){
_start:
{
size_t v_sz_boxed_1355_; size_t v_i_boxed_1356_; lean_object* v_res_1357_; 
v_sz_boxed_1355_ = lean_unbox_usize(v_sz_1352_);
lean_dec(v_sz_1352_);
v_i_boxed_1356_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1355_, v_i_boxed_1356_, v_bs_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(lean_object* v_inst_1358_, lean_object* v_declInfos_1359_, lean_object* v_k_1360_, uint8_t v_kind_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
size_t v_sz_1367_; size_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_sz_1367_ = lean_array_size(v_declInfos_1359_);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1367_, v___x_1368_, v_declInfos_1359_);
v___x_1370_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(v_inst_1358_, v___x_1369_, v_k_1360_, v_kind_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg___boxed(lean_object* v_inst_1371_, lean_object* v_declInfos_1372_, lean_object* v_k_1373_, lean_object* v_kind_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
uint8_t v_kind_boxed_1380_; lean_object* v_res_1381_; 
v_kind_boxed_1380_ = lean_unbox(v_kind_1374_);
v_res_1381_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(v_inst_1371_, v_declInfos_1372_, v_k_1373_, v_kind_boxed_1380_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v_inst_1371_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_snd_1382_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_1390_, lean_object* v_x_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_1390_, v_x_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec_ref(v_x_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_bs_1400_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_lt(v_i_1399_, v_sz_1398_);
if (v___x_1401_ == 0)
{
return v_bs_1400_;
}
else
{
lean_object* v_v_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1418_; 
v_v_1402_ = lean_array_uget(v_bs_1400_, v_i_1399_);
v_fst_1403_ = lean_ctor_get(v_v_1402_, 0);
v_snd_1404_ = lean_ctor_get(v_v_1402_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_v_1402_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1406_ = v_v_1402_;
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_v_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v_bs_x27_1409_; lean_object* v___f_1410_; lean_object* v___x_1412_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v_bs_x27_1409_ = lean_array_uset(v_bs_1400_, v_i_1399_, v___x_1408_);
v___f_1410_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1410_, 0, v_snd_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___f_1410_);
v___x_1412_ = v___x_1406_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___f_1410_);
v___x_1412_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1399_, v___x_1413_);
v___x_1415_ = lean_array_uset(v_bs_x27_1409_, v_i_1399_, v___x_1412_);
v_i_1399_ = v___x_1414_;
v_bs_1400_ = v___x_1415_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_bs_1421_){
_start:
{
size_t v_sz_boxed_1422_; size_t v_i_boxed_1423_; lean_object* v_res_1424_; 
v_sz_boxed_1422_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1423_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_1422_, v_i_boxed_1423_, v_bs_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(lean_object* v_inst_1425_, lean_object* v_declInfos_1426_, lean_object* v_k_1427_, uint8_t v_kind_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
size_t v_sz_1434_; size_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_sz_1434_ = lean_array_size(v_declInfos_1426_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1434_, v___x_1435_, v_declInfos_1426_);
v___x_1437_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(v_inst_1425_, v___x_1436_, v_k_1427_, v_kind_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg___boxed(lean_object* v_inst_1438_, lean_object* v_declInfos_1439_, lean_object* v_k_1440_, lean_object* v_kind_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_kind_boxed_1447_; lean_object* v_res_1448_; 
v_kind_boxed_1447_ = lean_unbox(v_kind_1441_);
v_res_1448_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v_inst_1438_, v_declInfos_1439_, v_k_1440_, v_kind_boxed_1447_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v_inst_1438_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1449_, lean_object* v_tail_1450_, lean_object* v_params_1451_, lean_object* v_numParams_1452_, lean_object* v_indName_1453_, lean_object* v_ism1_1454_, lean_object* v_ism2_1455_, lean_object* v___x_1456_, uint8_t v___x_1457_, uint8_t v___x_1458_, uint8_t v___x_1459_, lean_object* v_val_1460_, lean_object* v___x_1461_, lean_object* v___x_1462_, lean_object* v_name_1463_, lean_object* v___x_1464_, lean_object* v___x_1465_, lean_object* v_motive_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1472_ = lean_array_mk(v_ctors_1449_);
v___x_1473_ = lean_array_get_size(v___x_1472_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_mk_empty_array_with_capacity(v___x_1473_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc_ref(v_motive_1466_);
lean_inc(v_numParams_1452_);
lean_inc(v_tail_1450_);
v___x_1476_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1450_, v_params_1451_, v_numParams_1452_, v_motive_1466_, v___x_1472_, v___x_1473_, v___x_1474_, v___x_1475_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___f_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = lean_box(v___x_1457_);
v___x_1479_ = lean_box(v___x_1458_);
v___x_1480_ = lean_box(v___x_1459_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1481_, 0, v_indName_1453_);
lean_closure_set(v___f_1481_, 1, v_tail_1450_);
lean_closure_set(v___f_1481_, 2, v_params_1451_);
lean_closure_set(v___f_1481_, 3, v_ism1_1454_);
lean_closure_set(v___f_1481_, 4, v_ism2_1455_);
lean_closure_set(v___f_1481_, 5, v_motive_1466_);
lean_closure_set(v___f_1481_, 6, v___x_1456_);
lean_closure_set(v___f_1481_, 7, v___x_1478_);
lean_closure_set(v___f_1481_, 8, v___x_1479_);
lean_closure_set(v___f_1481_, 9, v___x_1480_);
lean_closure_set(v___f_1481_, 10, v___x_1472_);
lean_closure_set(v___f_1481_, 11, v_numParams_1452_);
lean_closure_set(v___f_1481_, 12, v_val_1460_);
lean_closure_set(v___f_1481_, 13, v___x_1461_);
lean_closure_set(v___f_1481_, 14, v___x_1462_);
lean_closure_set(v___f_1481_, 15, v_name_1463_);
lean_closure_set(v___f_1481_, 16, v___x_1464_);
v___x_1482_ = 0;
v___x_1483_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v___x_1465_, v_a_1477_, v___f_1481_, v___x_1482_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1483_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v___x_1472_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec_ref(v_motive_1466_);
lean_dec(v___x_1464_);
lean_dec(v_name_1463_);
lean_dec(v___x_1462_);
lean_dec(v___x_1461_);
lean_dec_ref(v_val_1460_);
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_ism2_1455_);
lean_dec_ref(v_ism1_1454_);
lean_dec(v_indName_1453_);
lean_dec(v_numParams_1452_);
lean_dec_ref(v_params_1451_);
lean_dec(v_tail_1450_);
v_a_1484_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1476_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1476_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1492_ = _args[0];
lean_object* v_tail_1493_ = _args[1];
lean_object* v_params_1494_ = _args[2];
lean_object* v_numParams_1495_ = _args[3];
lean_object* v_indName_1496_ = _args[4];
lean_object* v_ism1_1497_ = _args[5];
lean_object* v_ism2_1498_ = _args[6];
lean_object* v___x_1499_ = _args[7];
lean_object* v___x_1500_ = _args[8];
lean_object* v___x_1501_ = _args[9];
lean_object* v___x_1502_ = _args[10];
lean_object* v_val_1503_ = _args[11];
lean_object* v___x_1504_ = _args[12];
lean_object* v___x_1505_ = _args[13];
lean_object* v_name_1506_ = _args[14];
lean_object* v___x_1507_ = _args[15];
lean_object* v___x_1508_ = _args[16];
lean_object* v_motive_1509_ = _args[17];
lean_object* v___y_1510_ = _args[18];
lean_object* v___y_1511_ = _args[19];
lean_object* v___y_1512_ = _args[20];
lean_object* v___y_1513_ = _args[21];
lean_object* v___y_1514_ = _args[22];
_start:
{
uint8_t v___x_22725__boxed_1515_; uint8_t v___x_22726__boxed_1516_; uint8_t v___x_22727__boxed_1517_; lean_object* v_res_1518_; 
v___x_22725__boxed_1515_ = lean_unbox(v___x_1500_);
v___x_22726__boxed_1516_ = lean_unbox(v___x_1501_);
v___x_22727__boxed_1517_ = lean_unbox(v___x_1502_);
v_res_1518_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1492_, v_tail_1493_, v_params_1494_, v_numParams_1495_, v_indName_1496_, v_ism1_1497_, v_ism2_1498_, v___x_1499_, v___x_22725__boxed_1515_, v___x_22726__boxed_1516_, v___x_22727__boxed_1517_, v_val_1503_, v___x_1504_, v___x_1505_, v_name_1506_, v___x_1507_, v___x_1508_, v_motive_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec_ref(v___x_1508_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1522_, lean_object* v_head_1523_, lean_object* v_ctors_1524_, lean_object* v_tail_1525_, lean_object* v_params_1526_, lean_object* v_numParams_1527_, lean_object* v_indName_1528_, lean_object* v_val_1529_, lean_object* v___x_1530_, lean_object* v___x_1531_, lean_object* v_name_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_ism2_1535_, lean_object* v_x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; uint8_t v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
lean_inc_ref(v_ism1_1522_);
v___x_1542_ = l_Array_append___redArg(v_ism1_1522_, v_ism2_1535_);
v___x_1543_ = l_Lean_mkSort(v_head_1523_);
v___x_1544_ = 0;
v___x_1545_ = 1;
v___x_1546_ = 1;
v___x_1547_ = l_Lean_Meta_mkForallFVars(v___x_1542_, v___x_1543_, v___x_1544_, v___x_1545_, v___x_1545_, v___x_1546_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = lean_box(v___x_1544_);
v___x_1550_ = lean_box(v___x_1545_);
v___x_1551_ = lean_box(v___x_1546_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 23, 17);
lean_closure_set(v___f_1552_, 0, v_ctors_1524_);
lean_closure_set(v___f_1552_, 1, v_tail_1525_);
lean_closure_set(v___f_1552_, 2, v_params_1526_);
lean_closure_set(v___f_1552_, 3, v_numParams_1527_);
lean_closure_set(v___f_1552_, 4, v_indName_1528_);
lean_closure_set(v___f_1552_, 5, v_ism1_1522_);
lean_closure_set(v___f_1552_, 6, v_ism2_1535_);
lean_closure_set(v___f_1552_, 7, v___x_1542_);
lean_closure_set(v___f_1552_, 8, v___x_1549_);
lean_closure_set(v___f_1552_, 9, v___x_1550_);
lean_closure_set(v___f_1552_, 10, v___x_1551_);
lean_closure_set(v___f_1552_, 11, v_val_1529_);
lean_closure_set(v___f_1552_, 12, v___x_1530_);
lean_closure_set(v___f_1552_, 13, v___x_1531_);
lean_closure_set(v___f_1552_, 14, v_name_1532_);
lean_closure_set(v___f_1552_, 15, v___x_1533_);
lean_closure_set(v___f_1552_, 16, v___x_1534_);
v___x_1553_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1554_ = 0;
v___x_1555_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1553_, v___x_1546_, v_a_1548_, v___f_1552_, v___x_1554_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1555_;
}
else
{
lean_dec_ref(v___x_1542_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v_ism2_1535_);
lean_dec_ref(v___x_1534_);
lean_dec(v___x_1533_);
lean_dec(v_name_1532_);
lean_dec(v___x_1531_);
lean_dec(v___x_1530_);
lean_dec_ref(v_val_1529_);
lean_dec(v_indName_1528_);
lean_dec(v_numParams_1527_);
lean_dec_ref(v_params_1526_);
lean_dec(v_tail_1525_);
lean_dec(v_ctors_1524_);
lean_dec_ref(v_ism1_1522_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1556_ = _args[0];
lean_object* v_head_1557_ = _args[1];
lean_object* v_ctors_1558_ = _args[2];
lean_object* v_tail_1559_ = _args[3];
lean_object* v_params_1560_ = _args[4];
lean_object* v_numParams_1561_ = _args[5];
lean_object* v_indName_1562_ = _args[6];
lean_object* v_val_1563_ = _args[7];
lean_object* v___x_1564_ = _args[8];
lean_object* v___x_1565_ = _args[9];
lean_object* v_name_1566_ = _args[10];
lean_object* v___x_1567_ = _args[11];
lean_object* v___x_1568_ = _args[12];
lean_object* v_ism2_1569_ = _args[13];
lean_object* v_x_1570_ = _args[14];
lean_object* v___y_1571_ = _args[15];
lean_object* v___y_1572_ = _args[16];
lean_object* v___y_1573_ = _args[17];
lean_object* v___y_1574_ = _args[18];
lean_object* v___y_1575_ = _args[19];
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1556_, v_head_1557_, v_ctors_1558_, v_tail_1559_, v_params_1560_, v_numParams_1561_, v_indName_1562_, v_val_1563_, v___x_1564_, v___x_1565_, v_name_1566_, v___x_1567_, v___x_1568_, v_ism2_1569_, v_x_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec_ref(v_x_1570_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1577_, lean_object* v_ctors_1578_, lean_object* v_tail_1579_, lean_object* v_params_1580_, lean_object* v_numParams_1581_, lean_object* v_indName_1582_, lean_object* v_val_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_name_1586_, lean_object* v___x_1587_, lean_object* v___x_1588_, lean_object* v_t_1589_, lean_object* v___x_1590_, lean_object* v_ism1_1591_, lean_object* v_x_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___f_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 20, 13);
lean_closure_set(v___f_1598_, 0, v_ism1_1591_);
lean_closure_set(v___f_1598_, 1, v_head_1577_);
lean_closure_set(v___f_1598_, 2, v_ctors_1578_);
lean_closure_set(v___f_1598_, 3, v_tail_1579_);
lean_closure_set(v___f_1598_, 4, v_params_1580_);
lean_closure_set(v___f_1598_, 5, v_numParams_1581_);
lean_closure_set(v___f_1598_, 6, v_indName_1582_);
lean_closure_set(v___f_1598_, 7, v_val_1583_);
lean_closure_set(v___f_1598_, 8, v___x_1584_);
lean_closure_set(v___f_1598_, 9, v___x_1585_);
lean_closure_set(v___f_1598_, 10, v_name_1586_);
lean_closure_set(v___f_1598_, 11, v___x_1587_);
lean_closure_set(v___f_1598_, 12, v___x_1588_);
v___x_1599_ = 0;
v___x_1600_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1589_, v___x_1590_, v___f_1598_, v___x_1599_, v___x_1599_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1601_ = _args[0];
lean_object* v_ctors_1602_ = _args[1];
lean_object* v_tail_1603_ = _args[2];
lean_object* v_params_1604_ = _args[3];
lean_object* v_numParams_1605_ = _args[4];
lean_object* v_indName_1606_ = _args[5];
lean_object* v_val_1607_ = _args[6];
lean_object* v___x_1608_ = _args[7];
lean_object* v___x_1609_ = _args[8];
lean_object* v_name_1610_ = _args[9];
lean_object* v___x_1611_ = _args[10];
lean_object* v___x_1612_ = _args[11];
lean_object* v_t_1613_ = _args[12];
lean_object* v___x_1614_ = _args[13];
lean_object* v_ism1_1615_ = _args[14];
lean_object* v_x_1616_ = _args[15];
lean_object* v___y_1617_ = _args[16];
lean_object* v___y_1618_ = _args[17];
lean_object* v___y_1619_ = _args[18];
lean_object* v___y_1620_ = _args[19];
lean_object* v___y_1621_ = _args[20];
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1601_, v_ctors_1602_, v_tail_1603_, v_params_1604_, v_numParams_1605_, v_indName_1606_, v_val_1607_, v___x_1608_, v___x_1609_, v_name_1610_, v___x_1611_, v___x_1612_, v_t_1613_, v___x_1614_, v_ism1_1615_, v_x_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec_ref(v_x_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1623_, lean_object* v___x_1624_, lean_object* v_head_1625_, lean_object* v_ctors_1626_, lean_object* v_tail_1627_, lean_object* v_params_1628_, lean_object* v_numParams_1629_, lean_object* v_indName_1630_, lean_object* v_val_1631_, lean_object* v___x_1632_, lean_object* v___x_1633_, lean_object* v_name_1634_, lean_object* v___x_1635_, lean_object* v_x_1636_, lean_object* v_t_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___f_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; 
v___x_1643_ = lean_nat_add(v_numIndices_1623_, v___x_1624_);
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_inc_ref(v___x_1644_);
lean_inc_ref(v_t_1637_);
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 21, 14);
lean_closure_set(v___f_1645_, 0, v_head_1625_);
lean_closure_set(v___f_1645_, 1, v_ctors_1626_);
lean_closure_set(v___f_1645_, 2, v_tail_1627_);
lean_closure_set(v___f_1645_, 3, v_params_1628_);
lean_closure_set(v___f_1645_, 4, v_numParams_1629_);
lean_closure_set(v___f_1645_, 5, v_indName_1630_);
lean_closure_set(v___f_1645_, 6, v_val_1631_);
lean_closure_set(v___f_1645_, 7, v___x_1632_);
lean_closure_set(v___f_1645_, 8, v___x_1633_);
lean_closure_set(v___f_1645_, 9, v_name_1634_);
lean_closure_set(v___f_1645_, 10, v___x_1624_);
lean_closure_set(v___f_1645_, 11, v___x_1635_);
lean_closure_set(v___f_1645_, 12, v_t_1637_);
lean_closure_set(v___f_1645_, 13, v___x_1644_);
v___x_1646_ = 0;
v___x_1647_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1637_, v___x_1644_, v___f_1645_, v___x_1646_, v___x_1646_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1648_ = _args[0];
lean_object* v___x_1649_ = _args[1];
lean_object* v_head_1650_ = _args[2];
lean_object* v_ctors_1651_ = _args[3];
lean_object* v_tail_1652_ = _args[4];
lean_object* v_params_1653_ = _args[5];
lean_object* v_numParams_1654_ = _args[6];
lean_object* v_indName_1655_ = _args[7];
lean_object* v_val_1656_ = _args[8];
lean_object* v___x_1657_ = _args[9];
lean_object* v___x_1658_ = _args[10];
lean_object* v_name_1659_ = _args[11];
lean_object* v___x_1660_ = _args[12];
lean_object* v_x_1661_ = _args[13];
lean_object* v_t_1662_ = _args[14];
lean_object* v___y_1663_ = _args[15];
lean_object* v___y_1664_ = _args[16];
lean_object* v___y_1665_ = _args[17];
lean_object* v___y_1666_ = _args[18];
lean_object* v___y_1667_ = _args[19];
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1648_, v___x_1649_, v_head_1650_, v_ctors_1651_, v_tail_1652_, v_params_1653_, v_numParams_1654_, v_indName_1655_, v_val_1656_, v___x_1657_, v___x_1658_, v_name_1659_, v___x_1660_, v_x_1661_, v_t_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec_ref(v_x_1661_);
lean_dec(v_numIndices_1648_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1671_, lean_object* v_head_1672_, lean_object* v_ctors_1673_, lean_object* v_tail_1674_, lean_object* v_numParams_1675_, lean_object* v_indName_1676_, lean_object* v_val_1677_, lean_object* v___x_1678_, lean_object* v___x_1679_, lean_object* v_name_1680_, lean_object* v___x_1681_, lean_object* v_params_1682_, lean_object* v_t_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1689_ = lean_unsigned_to_nat(1u);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 20, 13);
lean_closure_set(v___f_1690_, 0, v_numIndices_1671_);
lean_closure_set(v___f_1690_, 1, v___x_1689_);
lean_closure_set(v___f_1690_, 2, v_head_1672_);
lean_closure_set(v___f_1690_, 3, v_ctors_1673_);
lean_closure_set(v___f_1690_, 4, v_tail_1674_);
lean_closure_set(v___f_1690_, 5, v_params_1682_);
lean_closure_set(v___f_1690_, 6, v_numParams_1675_);
lean_closure_set(v___f_1690_, 7, v_indName_1676_);
lean_closure_set(v___f_1690_, 8, v_val_1677_);
lean_closure_set(v___f_1690_, 9, v___x_1678_);
lean_closure_set(v___f_1690_, 10, v___x_1679_);
lean_closure_set(v___f_1690_, 11, v_name_1680_);
lean_closure_set(v___f_1690_, 12, v___x_1681_);
v___x_1691_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1692_ = 0;
v___x_1693_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1683_, v___x_1691_, v___f_1690_, v___x_1692_, v___x_1692_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1694_ = _args[0];
lean_object* v_head_1695_ = _args[1];
lean_object* v_ctors_1696_ = _args[2];
lean_object* v_tail_1697_ = _args[3];
lean_object* v_numParams_1698_ = _args[4];
lean_object* v_indName_1699_ = _args[5];
lean_object* v_val_1700_ = _args[6];
lean_object* v___x_1701_ = _args[7];
lean_object* v___x_1702_ = _args[8];
lean_object* v_name_1703_ = _args[9];
lean_object* v___x_1704_ = _args[10];
lean_object* v_params_1705_ = _args[11];
lean_object* v_t_1706_ = _args[12];
lean_object* v___y_1707_ = _args[13];
lean_object* v___y_1708_ = _args[14];
lean_object* v___y_1709_ = _args[15];
lean_object* v___y_1710_ = _args[16];
lean_object* v___y_1711_ = _args[17];
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1694_, v_head_1695_, v_ctors_1696_, v_tail_1697_, v_numParams_1698_, v_indName_1699_, v_val_1700_, v___x_1701_, v___x_1702_, v_name_1703_, v___x_1704_, v_params_1705_, v_t_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1713_, lean_object* v_declName_1714_, lean_object* v_levelParams_1715_, uint8_t v___x_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
lean_inc_ref(v_a_1713_);
v___x_1722_ = lean_infer_type(v_a_1713_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = lean_box(1);
v___x_1725_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1714_, v_levelParams_1715_, v_a_1723_, v_a_1713_, v___x_1724_, v___y_1720_);
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 1);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_addDecl(v___x_1731_, v___x_1716_, v___y_1719_, v___y_1720_);
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_levelParams_1715_);
lean_dec(v_declName_1714_);
lean_dec_ref(v_a_1713_);
v_a_1735_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1722_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1722_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1743_, lean_object* v_declName_1744_, lean_object* v_levelParams_1745_, lean_object* v___x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_23032__boxed_1752_; lean_object* v_res_1753_; 
v___x_23032__boxed_1752_ = lean_unbox(v___x_1746_);
v_res_1753_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1743_, v_declName_1744_, v_levelParams_1745_, v___x_23032__boxed_1752_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
if (lean_obj_tag(v_a_1754_) == 0)
{
lean_object* v___x_1756_; 
v___x_1756_ = l_List_reverse___redArg(v_a_1755_);
return v___x_1756_;
}
else
{
lean_object* v_head_1757_; lean_object* v_tail_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1767_; 
v_head_1757_ = lean_ctor_get(v_a_1754_, 0);
v_tail_1758_ = lean_ctor_get(v_a_1754_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1760_ = v_a_1754_;
v_isShared_1761_ = v_isSharedCheck_1767_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_tail_1758_);
lean_inc(v_head_1757_);
lean_dec(v_a_1754_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1767_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l_Lean_mkLevelParam(v_head_1757_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v_a_1755_);
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_a_1755_);
v___x_1764_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
v_a_1754_ = v_tail_1758_;
v_a_1755_ = v___x_1764_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v_env_1775_; lean_object* v___x_1776_; lean_object* v_mctx_1777_; lean_object* v_lctx_1778_; lean_object* v_options_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1774_ = lean_st_ref_get(v___y_1772_);
v_env_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref(v_env_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = lean_st_ref_get(v___y_1770_);
v_mctx_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_mctx_1777_);
lean_dec(v___x_1776_);
v_lctx_1778_ = lean_ctor_get(v___y_1769_, 2);
v_options_1779_ = lean_ctor_get(v___y_1771_, 2);
lean_inc_ref(v_options_1779_);
lean_inc_ref(v_lctx_1778_);
v___x_1780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1780_, 0, v_env_1775_);
lean_ctor_set(v___x_1780_, 1, v_mctx_1777_);
lean_ctor_set(v___x_1780_, 2, v_lctx_1778_);
lean_ctor_set(v___x_1780_, 3, v_options_1779_);
v___x_1781_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v_msgData_1768_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_ref_1796_; lean_object* v___x_1797_; lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_ref_1796_ = lean_ctor_get(v___y_1793_, 5);
v___x_1797_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_inc(v_ref_1796_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v_ref_1796_);
lean_ctor_set(v___x_1802_, 1, v_a_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 1);
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1814_, lean_object* v_msg_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_fileName_1821_; lean_object* v_fileMap_1822_; lean_object* v_options_1823_; lean_object* v_currRecDepth_1824_; lean_object* v_maxRecDepth_1825_; lean_object* v_ref_1826_; lean_object* v_currNamespace_1827_; lean_object* v_openDecls_1828_; lean_object* v_initHeartbeats_1829_; lean_object* v_maxHeartbeats_1830_; lean_object* v_quotContext_1831_; lean_object* v_currMacroScope_1832_; uint8_t v_diag_1833_; lean_object* v_cancelTk_x3f_1834_; uint8_t v_suppressElabErrors_1835_; lean_object* v_inheritedTraceOptions_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
v_fileName_1821_ = lean_ctor_get(v___y_1818_, 0);
v_fileMap_1822_ = lean_ctor_get(v___y_1818_, 1);
v_options_1823_ = lean_ctor_get(v___y_1818_, 2);
v_currRecDepth_1824_ = lean_ctor_get(v___y_1818_, 3);
v_maxRecDepth_1825_ = lean_ctor_get(v___y_1818_, 4);
v_ref_1826_ = lean_ctor_get(v___y_1818_, 5);
v_currNamespace_1827_ = lean_ctor_get(v___y_1818_, 6);
v_openDecls_1828_ = lean_ctor_get(v___y_1818_, 7);
v_initHeartbeats_1829_ = lean_ctor_get(v___y_1818_, 8);
v_maxHeartbeats_1830_ = lean_ctor_get(v___y_1818_, 9);
v_quotContext_1831_ = lean_ctor_get(v___y_1818_, 10);
v_currMacroScope_1832_ = lean_ctor_get(v___y_1818_, 11);
v_diag_1833_ = lean_ctor_get_uint8(v___y_1818_, sizeof(void*)*14);
v_cancelTk_x3f_1834_ = lean_ctor_get(v___y_1818_, 12);
v_suppressElabErrors_1835_ = lean_ctor_get_uint8(v___y_1818_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1836_ = lean_ctor_get(v___y_1818_, 13);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___y_1818_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1838_ = v___y_1818_;
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_inheritedTraceOptions_1836_);
lean_inc(v_cancelTk_x3f_1834_);
lean_inc(v_currMacroScope_1832_);
lean_inc(v_quotContext_1831_);
lean_inc(v_maxHeartbeats_1830_);
lean_inc(v_initHeartbeats_1829_);
lean_inc(v_openDecls_1828_);
lean_inc(v_currNamespace_1827_);
lean_inc(v_ref_1826_);
lean_inc(v_maxRecDepth_1825_);
lean_inc(v_currRecDepth_1824_);
lean_inc(v_options_1823_);
lean_inc(v_fileMap_1822_);
lean_inc(v_fileName_1821_);
lean_dec(v___y_1818_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_ref_1840_; lean_object* v___x_1842_; 
v_ref_1840_ = l_Lean_replaceRef(v_ref_1814_, v_ref_1826_);
lean_dec(v_ref_1826_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 5, v_ref_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_fileName_1821_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_fileMap_1822_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_options_1823_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_currRecDepth_1824_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_maxRecDepth_1825_);
lean_ctor_set(v_reuseFailAlloc_1844_, 5, v_ref_1840_);
lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_currNamespace_1827_);
lean_ctor_set(v_reuseFailAlloc_1844_, 7, v_openDecls_1828_);
lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_initHeartbeats_1829_);
lean_ctor_set(v_reuseFailAlloc_1844_, 9, v_maxHeartbeats_1830_);
lean_ctor_set(v_reuseFailAlloc_1844_, 10, v_quotContext_1831_);
lean_ctor_set(v_reuseFailAlloc_1844_, 11, v_currMacroScope_1832_);
lean_ctor_set(v_reuseFailAlloc_1844_, 12, v_cancelTk_x3f_1834_);
lean_ctor_set(v_reuseFailAlloc_1844_, 13, v_inheritedTraceOptions_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*14, v_diag_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*14 + 1, v_suppressElabErrors_1835_);
v___x_1842_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1815_, v___y_1816_, v___y_1817_, v___x_1842_, v___y_1819_);
lean_dec_ref(v___x_1842_);
return v___x_1843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1846_, lean_object* v_msg_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1846_, v_msg_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v_ref_1846_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
lean_ctor_set(v___x_1859_, 2, v___x_1858_);
lean_ctor_set(v___x_1859_, 3, v___x_1857_);
lean_ctor_set(v___x_1859_, 4, v___x_1857_);
lean_ctor_set(v___x_1859_, 5, v___x_1857_);
lean_ctor_set(v___x_1859_, 6, v___x_1857_);
lean_ctor_set(v___x_1859_, 7, v___x_1857_);
lean_ctor_set(v___x_1859_, 8, v___x_1857_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(32u);
v___x_1861_ = lean_mk_empty_array_with_capacity(v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1863_ = ((size_t)5ULL);
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_unsigned_to_nat(32u);
v___x_1866_ = lean_mk_empty_array_with_capacity(v___x_1865_);
v___x_1867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1868_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1866_);
lean_ctor_set(v___x_1868_, 2, v___x_1864_);
lean_ctor_set(v___x_1868_, 3, v___x_1864_);
lean_ctor_set_usize(v___x_1868_, 4, v___x_1863_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = lean_box(1);
v___x_1870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1870_);
lean_ctor_set(v___x_1872_, 2, v___x_1869_);
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1878_ = l_Lean_stringToMessageData(v___x_1877_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1884_ = l_Lean_stringToMessageData(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1890_ = l_Lean_stringToMessageData(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1893_ = l_Lean_stringToMessageData(v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1894_, lean_object* v_declHint_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; lean_object* v_env_1899_; uint8_t v___x_1900_; 
v___x_1898_ = lean_st_ref_get(v___y_1896_);
v_env_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc_ref(v_env_1899_);
lean_dec(v___x_1898_);
v___x_1900_ = l_Lean_Name_isAnonymous(v_declHint_1895_);
if (v___x_1900_ == 0)
{
uint8_t v_isExporting_1901_; 
v_isExporting_1901_ = lean_ctor_get_uint8(v_env_1899_, sizeof(void*)*8);
if (v_isExporting_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v_env_1899_);
lean_dec(v_declHint_1895_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_msg_1894_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
lean_inc_ref(v_env_1899_);
v___x_1903_ = l_Lean_Environment_setExporting(v_env_1899_, v___x_1900_);
lean_inc(v_declHint_1895_);
lean_inc_ref(v___x_1903_);
v___x_1904_ = l_Lean_Environment_contains(v___x_1903_, v_declHint_1895_, v_isExporting_1901_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
lean_dec_ref(v___x_1903_);
lean_dec_ref(v_env_1899_);
lean_dec(v_declHint_1895_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_msg_1894_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_c_1911_; lean_object* v___x_1912_; 
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1907_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1908_ = l_Lean_Options_empty;
v___x_1909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1903_);
lean_ctor_set(v___x_1909_, 1, v___x_1906_);
lean_ctor_set(v___x_1909_, 2, v___x_1907_);
lean_ctor_set(v___x_1909_, 3, v___x_1908_);
lean_inc(v_declHint_1895_);
v___x_1910_ = l_Lean_MessageData_ofConstName(v_declHint_1895_, v___x_1900_);
v_c_1911_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1911_, 0, v___x_1909_);
lean_ctor_set(v_c_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1899_, v_declHint_1895_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec_ref(v_env_1899_);
lean_dec(v_declHint_1895_);
v___x_1913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v_c_1911_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_MessageData_note(v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_msg_1894_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
else
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1955_; 
v_val_1920_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1922_ = v___x_1912_;
v_isShared_1923_ = v_isSharedCheck_1955_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1912_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1955_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_mod_1927_; uint8_t v___x_1928_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = l_Lean_Environment_header(v_env_1899_);
lean_dec_ref(v_env_1899_);
v___x_1926_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1925_);
v_mod_1927_ = lean_array_get(v___x_1924_, v___x_1926_, v_val_1920_);
lean_dec(v_val_1920_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = l_Lean_isPrivateName(v_declHint_1895_);
lean_dec(v_declHint_1895_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1929_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_c_1911_);
v___x_1931_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l_Lean_MessageData_ofName(v_mod_1927_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_MessageData_note(v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_msg_1894_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1938_);
v___x_1940_ = v___x_1922_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v_c_1911_);
v___x_1944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Lean_MessageData_ofName(v_mod_1927_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_MessageData_note(v___x_1949_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_msg_1894_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1951_);
v___x_1953_ = v___x_1922_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1956_; 
lean_dec_ref(v_env_1899_);
lean_dec(v_declHint_1895_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_msg_1894_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1957_, lean_object* v_declHint_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1957_, v_declHint_1958_, v___y_1959_);
lean_dec(v___y_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1962_, lean_object* v_declHint_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1979_; 
v___x_1969_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1962_, v_declHint_1963_, v___y_1967_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = l_Lean_unknownIdentifierMessageTag;
v___x_1975_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1975_);
v___x_1977_ = v___x_1972_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1980_, lean_object* v_declHint_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1988_, lean_object* v_msg_1989_, lean_object* v_declHint_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v_a_1997_; lean_object* v___x_1998_; 
v___x_1996_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1989_, v_declHint_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1988_, v_a_1997_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1999_, lean_object* v_msg_2000_, lean_object* v_declHint_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1999_, v_msg_2000_, v_declHint_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_ref_1999_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_2014_, lean_object* v_constName_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2021_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_2022_ = 0;
lean_inc(v_constName_2015_);
v___x_2023_ = l_Lean_MessageData_ofConstName(v_constName_2015_, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2021_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2014_, v___x_2026_, v_constName_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_2028_, lean_object* v_constName_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2028_, v_constName_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v_ref_2028_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_ref_2042_; lean_object* v___x_2043_; 
v_ref_2042_ = lean_ctor_get(v___y_2039_, 5);
lean_inc(v_ref_2042_);
v___x_2043_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2042_, v_constName_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v_ref_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v_env_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2057_ = lean_st_ref_get(v___y_2055_);
v_env_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_ref(v_env_2058_);
lean_dec(v___x_2057_);
v___x_2059_ = 0;
lean_inc(v_constName_2051_);
v___x_2060_ = l_Lean_Environment_findConstVal_x3f(v_env_2058_, v_constName_2051_, v___x_2059_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
return v___x_2061_;
}
else
{
lean_object* v_val_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v___y_2054_);
lean_dec(v_constName_2051_);
v_val_2062_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2060_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_val_2062_);
lean_dec(v___x_2060_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 0);
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2077_, uint8_t v_s_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v_env_2083_; lean_object* v_nextMacroScope_2084_; lean_object* v_ngen_2085_; lean_object* v_auxDeclNGen_2086_; lean_object* v_traceState_2087_; lean_object* v_messages_2088_; lean_object* v_infoState_2089_; lean_object* v_snapshotTasks_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2119_; 
v___x_2082_ = lean_st_ref_take(v___y_2080_);
v_env_2083_ = lean_ctor_get(v___x_2082_, 0);
v_nextMacroScope_2084_ = lean_ctor_get(v___x_2082_, 1);
v_ngen_2085_ = lean_ctor_get(v___x_2082_, 2);
v_auxDeclNGen_2086_ = lean_ctor_get(v___x_2082_, 3);
v_traceState_2087_ = lean_ctor_get(v___x_2082_, 4);
v_messages_2088_ = lean_ctor_get(v___x_2082_, 6);
v_infoState_2089_ = lean_ctor_get(v___x_2082_, 7);
v_snapshotTasks_2090_ = lean_ctor_get(v___x_2082_, 8);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v___x_2082_, 5);
lean_dec(v_unused_2120_);
v___x_2092_ = v___x_2082_;
v_isShared_2093_ = v_isSharedCheck_2119_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_snapshotTasks_2090_);
lean_inc(v_infoState_2089_);
lean_inc(v_messages_2088_);
lean_inc(v_traceState_2087_);
lean_inc(v_auxDeclNGen_2086_);
lean_inc(v_ngen_2085_);
lean_inc(v_nextMacroScope_2084_);
lean_inc(v_env_2083_);
lean_dec(v___x_2082_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2119_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2094_ = 0;
v___x_2095_ = lean_box(0);
v___x_2096_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2083_, v_declName_2077_, v_s_2078_, v___x_2094_, v___x_2095_);
v___x_2097_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 5, v___x_2097_);
lean_ctor_set(v___x_2092_, 0, v___x_2096_);
v___x_2099_ = v___x_2092_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_nextMacroScope_2084_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_ngen_2085_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_auxDeclNGen_2086_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_traceState_2087_);
lean_ctor_set(v_reuseFailAlloc_2118_, 5, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2118_, 6, v_messages_2088_);
lean_ctor_set(v_reuseFailAlloc_2118_, 7, v_infoState_2089_);
lean_ctor_set(v_reuseFailAlloc_2118_, 8, v_snapshotTasks_2090_);
v___x_2099_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_mctx_2102_; lean_object* v_zetaDeltaFVarIds_2103_; lean_object* v_postponed_2104_; lean_object* v_diag_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2116_; 
v___x_2100_ = lean_st_ref_set(v___y_2080_, v___x_2099_);
v___x_2101_ = lean_st_ref_take(v___y_2079_);
v_mctx_2102_ = lean_ctor_get(v___x_2101_, 0);
v_zetaDeltaFVarIds_2103_ = lean_ctor_get(v___x_2101_, 2);
v_postponed_2104_ = lean_ctor_get(v___x_2101_, 3);
v_diag_2105_ = lean_ctor_get(v___x_2101_, 4);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2101_, 1);
lean_dec(v_unused_2117_);
v___x_2107_ = v___x_2101_;
v_isShared_2108_ = v_isSharedCheck_2116_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_diag_2105_);
lean_inc(v_postponed_2104_);
lean_inc(v_zetaDeltaFVarIds_2103_);
lean_inc(v_mctx_2102_);
lean_dec(v___x_2101_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2116_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v___x_2109_);
v___x_2111_ = v___x_2107_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_mctx_2102_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_zetaDeltaFVarIds_2103_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_postponed_2104_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_diag_2105_);
v___x_2111_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_st_ref_set(v___y_2079_, v___x_2111_);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2121_, lean_object* v_s_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
uint8_t v_s_boxed_2126_; lean_object* v_res_2127_; 
v_s_boxed_2126_ = lean_unbox(v_s_2122_);
v_res_2127_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2121_, v_s_boxed_2126_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec(v___y_2123_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = 0;
v___x_2135_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2128_, v___x_2134_, v___y_2130_, v___y_2132_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2142_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2152_, lean_object* v_declName_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2159_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2160_ = l_Lean_MessageData_ofName(v_attrName_2152_);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = 0;
v___x_2165_ = l_Lean_MessageData_ofConstName(v_declName_2153_, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2163_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2168_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2170_, lean_object* v_declName_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2170_, v_declName_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
return v_res_2177_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2180_ = l_Lean_stringToMessageData(v___x_2179_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2183_ = l_Lean_stringToMessageData(v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2184_, lean_object* v_declName_2185_, lean_object* v_asyncPrefix_x3f_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___y_2193_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2186_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_MessageData_nil;
v___y_2193_ = v___x_2206_;
goto v___jp_2192_;
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_val_2207_ = lean_ctor_get(v_asyncPrefix_x3f_2186_, 0);
lean_inc(v_val_2207_);
lean_dec_ref(v_asyncPrefix_x3f_2186_);
v___x_2208_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2209_ = l_Lean_MessageData_ofName(v_val_2207_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___y_2193_ = v___x_2212_;
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2194_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2195_ = l_Lean_MessageData_ofName(v_attrName_2184_);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = 0;
v___x_2200_ = l_Lean_MessageData_ofConstName(v_declName_2185_, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2198_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___y_2193_);
v___x_2205_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2204_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2213_, lean_object* v_declName_2214_, lean_object* v_asyncPrefix_x3f_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2213_, v_declName_2214_, v_asyncPrefix_x3f_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2222_, lean_object* v_decl_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___x_2272_; lean_object* v_env_2273_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___x_2288_; 
v___x_2272_ = lean_st_ref_get(v___y_2227_);
v_env_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc_ref(v_env_2273_);
lean_dec(v___x_2272_);
v___x_2288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2273_, v_decl_2223_);
if (lean_obj_tag(v___x_2288_) == 0)
{
v___y_2275_ = v___y_2224_;
v___y_2276_ = v___y_2225_;
v___y_2277_ = v___y_2226_;
v___y_2278_ = v___y_2227_;
goto v___jp_2274_;
}
else
{
lean_object* v_attr_2289_; lean_object* v_toAttributeImplCore_2290_; lean_object* v_name_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v___x_2288_);
lean_dec_ref(v_env_2273_);
v_attr_2289_ = lean_ctor_get(v_attr_2222_, 0);
lean_inc_ref(v_attr_2289_);
lean_dec_ref(v_attr_2222_);
v_toAttributeImplCore_2290_ = lean_ctor_get(v_attr_2289_, 0);
lean_inc_ref(v_toAttributeImplCore_2290_);
lean_dec_ref(v_attr_2289_);
v_name_2291_ = lean_ctor_get(v_toAttributeImplCore_2290_, 1);
lean_inc(v_name_2291_);
lean_dec_ref(v_toAttributeImplCore_2290_);
v___x_2292_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2291_, v_decl_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2292_;
}
v___jp_2229_:
{
lean_object* v___x_2232_; lean_object* v_ext_2233_; lean_object* v_toEnvExtension_2234_; lean_object* v_env_2235_; lean_object* v_nextMacroScope_2236_; lean_object* v_ngen_2237_; lean_object* v_auxDeclNGen_2238_; lean_object* v_traceState_2239_; lean_object* v_messages_2240_; lean_object* v_infoState_2241_; lean_object* v_snapshotTasks_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2270_; 
v___x_2232_ = lean_st_ref_take(v___y_2231_);
v_ext_2233_ = lean_ctor_get(v_attr_2222_, 1);
lean_inc_ref(v_ext_2233_);
lean_dec_ref(v_attr_2222_);
v_toEnvExtension_2234_ = lean_ctor_get(v_ext_2233_, 0);
v_env_2235_ = lean_ctor_get(v___x_2232_, 0);
v_nextMacroScope_2236_ = lean_ctor_get(v___x_2232_, 1);
v_ngen_2237_ = lean_ctor_get(v___x_2232_, 2);
v_auxDeclNGen_2238_ = lean_ctor_get(v___x_2232_, 3);
v_traceState_2239_ = lean_ctor_get(v___x_2232_, 4);
v_messages_2240_ = lean_ctor_get(v___x_2232_, 6);
v_infoState_2241_ = lean_ctor_get(v___x_2232_, 7);
v_snapshotTasks_2242_ = lean_ctor_get(v___x_2232_, 8);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v___x_2232_, 5);
lean_dec(v_unused_2271_);
v___x_2244_ = v___x_2232_;
v_isShared_2245_ = v_isSharedCheck_2270_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snapshotTasks_2242_);
lean_inc(v_infoState_2241_);
lean_inc(v_messages_2240_);
lean_inc(v_traceState_2239_);
lean_inc(v_auxDeclNGen_2238_);
lean_inc(v_ngen_2237_);
lean_inc(v_nextMacroScope_2236_);
lean_inc(v_env_2235_);
lean_dec(v___x_2232_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2270_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v_asyncMode_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v_asyncMode_2246_ = lean_ctor_get(v_toEnvExtension_2234_, 2);
lean_inc(v_asyncMode_2246_);
lean_inc(v_decl_2223_);
v___x_2247_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2233_, v_env_2235_, v_decl_2223_, v_asyncMode_2246_, v_decl_2223_);
lean_dec(v_asyncMode_2246_);
v___x_2248_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 5, v___x_2248_);
lean_ctor_set(v___x_2244_, 0, v___x_2247_);
v___x_2250_ = v___x_2244_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_nextMacroScope_2236_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_ngen_2237_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_auxDeclNGen_2238_);
lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_traceState_2239_);
lean_ctor_set(v_reuseFailAlloc_2269_, 5, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2269_, 6, v_messages_2240_);
lean_ctor_set(v_reuseFailAlloc_2269_, 7, v_infoState_2241_);
lean_ctor_set(v_reuseFailAlloc_2269_, 8, v_snapshotTasks_2242_);
v___x_2250_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_mctx_2253_; lean_object* v_zetaDeltaFVarIds_2254_; lean_object* v_postponed_2255_; lean_object* v_diag_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2267_; 
v___x_2251_ = lean_st_ref_set(v___y_2231_, v___x_2250_);
v___x_2252_ = lean_st_ref_take(v___y_2230_);
v_mctx_2253_ = lean_ctor_get(v___x_2252_, 0);
v_zetaDeltaFVarIds_2254_ = lean_ctor_get(v___x_2252_, 2);
v_postponed_2255_ = lean_ctor_get(v___x_2252_, 3);
v_diag_2256_ = lean_ctor_get(v___x_2252_, 4);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v___x_2252_, 1);
lean_dec(v_unused_2268_);
v___x_2258_ = v___x_2252_;
v_isShared_2259_ = v_isSharedCheck_2267_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_diag_2256_);
lean_inc(v_postponed_2255_);
lean_inc(v_zetaDeltaFVarIds_2254_);
lean_inc(v_mctx_2253_);
lean_dec(v___x_2252_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2267_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___x_2260_);
v___x_2262_ = v___x_2258_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_mctx_2253_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_zetaDeltaFVarIds_2254_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_postponed_2255_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v_diag_2256_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_st_ref_set(v___y_2230_, v___x_2262_);
v___x_2264_ = lean_box(0);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
}
}
}
}
v___jp_2274_:
{
lean_object* v_ext_2279_; lean_object* v_toEnvExtension_2280_; lean_object* v_attr_2281_; lean_object* v_asyncMode_2282_; uint8_t v___x_2283_; 
v_ext_2279_ = lean_ctor_get(v_attr_2222_, 1);
v_toEnvExtension_2280_ = lean_ctor_get(v_ext_2279_, 0);
v_attr_2281_ = lean_ctor_get(v_attr_2222_, 0);
v_asyncMode_2282_ = lean_ctor_get(v_toEnvExtension_2280_, 2);
lean_inc(v_decl_2223_);
lean_inc_ref(v_env_2273_);
v___x_2283_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2273_, v_decl_2223_, v_asyncMode_2282_);
if (v___x_2283_ == 0)
{
lean_object* v_toAttributeImplCore_2284_; lean_object* v_name_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_inc_ref(v_attr_2281_);
lean_dec_ref(v_attr_2222_);
v_toAttributeImplCore_2284_ = lean_ctor_get(v_attr_2281_, 0);
lean_inc_ref(v_toAttributeImplCore_2284_);
lean_dec_ref(v_attr_2281_);
v_name_2285_ = lean_ctor_get(v_toAttributeImplCore_2284_, 1);
lean_inc(v_name_2285_);
lean_dec_ref(v_toAttributeImplCore_2284_);
v___x_2286_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2273_);
v___x_2287_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2285_, v_decl_2223_, v___x_2286_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2287_;
}
else
{
lean_dec_ref(v_env_2273_);
v___y_2230_ = v___y_2276_;
v___y_2231_ = v___y_2278_;
goto v___jp_2229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2293_, lean_object* v_decl_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2293_, v_decl_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v_env_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2307_ = lean_st_ref_get(v___y_2305_);
v_env_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc_ref(v_env_2308_);
lean_dec(v___x_2307_);
v___x_2309_ = 0;
lean_inc(v_constName_2301_);
v___x_2310_ = l_Lean_Environment_find_x3f(v_env_2308_, v_constName_2301_, v___x_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2311_;
}
else
{
lean_object* v_val_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___y_2304_);
lean_dec(v_constName_2301_);
v_val_2312_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2310_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_val_2312_);
lean_dec(v___x_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 0);
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_val_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2326_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2330_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2331_ = lean_unsigned_to_nat(58u);
v___x_2332_ = lean_unsigned_to_nat(33u);
v___x_2333_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2334_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2335_ = l_mkPanicMessageWithDecl(v___x_2334_, v___x_2333_, v___x_2332_, v___x_2331_, v___x_2330_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2337_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2338_ = lean_unsigned_to_nat(60u);
v___x_2339_ = lean_unsigned_to_nat(30u);
v___x_2340_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2341_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2342_ = l_mkPanicMessageWithDecl(v___x_2341_, v___x_2340_, v___x_2339_, v___x_2338_, v___x_2337_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2343_, lean_object* v_indName_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; 
lean_inc_ref(v_a_2347_);
lean_inc(v_indName_2344_);
v___x_2350_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
if (lean_obj_tag(v_a_2351_) == 5)
{
lean_object* v_val_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2539_; 
v_val_2352_ = lean_ctor_get(v_a_2351_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_a_2351_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2354_ = v_a_2351_;
v_isShared_2355_ = v_isSharedCheck_2539_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_val_2352_);
lean_dec(v_a_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2539_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_inc(v_indName_2344_);
v___x_2356_ = l_Lean_mkCasesOnName(v_indName_2344_);
lean_inc_ref(v_a_2347_);
lean_inc(v___x_2356_);
v___x_2357_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2356_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v_name_2359_; lean_object* v_levelParams_2360_; lean_object* v_type_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v_name_2359_ = lean_ctor_get(v_a_2358_, 0);
lean_inc(v_name_2359_);
v_levelParams_2360_ = lean_ctor_get(v_a_2358_, 1);
lean_inc(v_levelParams_2360_);
v_type_2361_ = lean_ctor_get(v_a_2358_, 2);
lean_inc_ref(v_type_2361_);
lean_dec(v_a_2358_);
v___x_2362_ = lean_box(0);
lean_inc(v_levelParams_2360_);
v___x_2363_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2360_, v___x_2362_);
if (lean_obj_tag(v___x_2363_) == 1)
{
lean_object* v_head_2364_; lean_object* v_tail_2365_; lean_object* v_numParams_2366_; lean_object* v_numIndices_2367_; lean_object* v_ctors_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v___x_2372_; 
v_head_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_head_2364_);
v_tail_2365_ = lean_ctor_get(v___x_2363_, 1);
lean_inc(v_tail_2365_);
v_numParams_2366_ = lean_ctor_get(v_val_2352_, 1);
lean_inc(v_numParams_2366_);
v_numIndices_2367_ = lean_ctor_get(v_val_2352_, 2);
lean_inc(v_numIndices_2367_);
v_ctors_2368_ = lean_ctor_get(v_val_2352_, 4);
lean_inc(v_ctors_2368_);
v___x_2369_ = l_Lean_instInhabitedExpr;
lean_inc(v_numParams_2366_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 18, 11);
lean_closure_set(v___f_2370_, 0, v_numIndices_2367_);
lean_closure_set(v___f_2370_, 1, v_head_2364_);
lean_closure_set(v___f_2370_, 2, v_ctors_2368_);
lean_closure_set(v___f_2370_, 3, v_tail_2365_);
lean_closure_set(v___f_2370_, 4, v_numParams_2366_);
lean_closure_set(v___f_2370_, 5, v_indName_2344_);
lean_closure_set(v___f_2370_, 6, v_val_2352_);
lean_closure_set(v___f_2370_, 7, v___x_2363_);
lean_closure_set(v___f_2370_, 8, v___x_2356_);
lean_closure_set(v___f_2370_, 9, v_name_2359_);
lean_closure_set(v___f_2370_, 10, v___x_2369_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 1);
lean_ctor_set(v___x_2354_, 0, v_numParams_2366_);
v___x_2372_ = v___x_2354_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_numParams_2366_);
v___x_2372_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
uint8_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = 0;
lean_inc(v_a_2348_);
lean_inc_ref(v_a_2347_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
v___x_2374_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2361_, v___x_2372_, v___f_2370_, v___x_2373_, v___x_2373_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; uint8_t v___y_2379_; uint8_t v___x_2518_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = lean_box(v___x_2373_);
lean_inc(v_declName_2343_);
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2377_, 0, v_a_2375_);
lean_closure_set(v___f_2377_, 1, v_declName_2343_);
lean_closure_set(v___f_2377_, 2, v_levelParams_2360_);
lean_closure_set(v___f_2377_, 3, v___x_2376_);
v___x_2518_ = l_Lean_isPrivateName(v_declName_2343_);
if (v___x_2518_ == 0)
{
uint8_t v___x_2519_; 
v___x_2519_ = 1;
v___y_2379_ = v___x_2519_;
goto v___jp_2378_;
}
else
{
v___y_2379_ = v___x_2373_;
goto v___jp_2378_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; 
lean_inc(v_a_2348_);
lean_inc_ref(v_a_2347_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
v___x_2380_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2377_, v___y_2379_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v___x_2381_; lean_object* v_env_2382_; lean_object* v_nextMacroScope_2383_; lean_object* v_ngen_2384_; lean_object* v_auxDeclNGen_2385_; lean_object* v_traceState_2386_; lean_object* v_messages_2387_; lean_object* v_infoState_2388_; lean_object* v_snapshotTasks_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v___x_2380_);
v___x_2381_ = lean_st_ref_take(v_a_2348_);
v_env_2382_ = lean_ctor_get(v___x_2381_, 0);
v_nextMacroScope_2383_ = lean_ctor_get(v___x_2381_, 1);
v_ngen_2384_ = lean_ctor_get(v___x_2381_, 2);
v_auxDeclNGen_2385_ = lean_ctor_get(v___x_2381_, 3);
v_traceState_2386_ = lean_ctor_get(v___x_2381_, 4);
v_messages_2387_ = lean_ctor_get(v___x_2381_, 6);
v_infoState_2388_ = lean_ctor_get(v___x_2381_, 7);
v_snapshotTasks_2389_ = lean_ctor_get(v___x_2381_, 8);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2381_, 5);
lean_dec(v_unused_2517_);
v___x_2391_ = v___x_2381_;
v_isShared_2392_ = v_isSharedCheck_2516_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_snapshotTasks_2389_);
lean_inc(v_infoState_2388_);
lean_inc(v_messages_2387_);
lean_inc(v_traceState_2386_);
lean_inc(v_auxDeclNGen_2385_);
lean_inc(v_ngen_2384_);
lean_inc(v_nextMacroScope_2383_);
lean_inc(v_env_2382_);
lean_dec(v___x_2381_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2516_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
lean_inc(v_declName_2343_);
v___x_2393_ = l_Lean_Meta_markMatcherLike(v_env_2382_, v_declName_2343_);
v___x_2394_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 5, v___x_2394_);
lean_ctor_set(v___x_2391_, 0, v___x_2393_);
v___x_2396_ = v___x_2391_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_nextMacroScope_2383_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_ngen_2384_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_auxDeclNGen_2385_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_traceState_2386_);
lean_ctor_set(v_reuseFailAlloc_2515_, 5, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2515_, 6, v_messages_2387_);
lean_ctor_set(v_reuseFailAlloc_2515_, 7, v_infoState_2388_);
lean_ctor_set(v_reuseFailAlloc_2515_, 8, v_snapshotTasks_2389_);
v___x_2396_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_mctx_2399_; lean_object* v_zetaDeltaFVarIds_2400_; lean_object* v_postponed_2401_; lean_object* v_diag_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2513_; 
v___x_2397_ = lean_st_ref_set(v_a_2348_, v___x_2396_);
v___x_2398_ = lean_st_ref_take(v_a_2346_);
v_mctx_2399_ = lean_ctor_get(v___x_2398_, 0);
v_zetaDeltaFVarIds_2400_ = lean_ctor_get(v___x_2398_, 2);
v_postponed_2401_ = lean_ctor_get(v___x_2398_, 3);
v_diag_2402_ = lean_ctor_get(v___x_2398_, 4);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v___x_2398_, 1);
lean_dec(v_unused_2514_);
v___x_2404_ = v___x_2398_;
v_isShared_2405_ = v_isSharedCheck_2513_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_diag_2402_);
lean_inc(v_postponed_2401_);
lean_inc(v_zetaDeltaFVarIds_2400_);
lean_inc(v_mctx_2399_);
lean_dec(v___x_2398_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2513_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 1, v___x_2406_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_mctx_2399_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_zetaDeltaFVarIds_2400_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_postponed_2401_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_diag_2402_);
v___x_2408_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v_env_2411_; lean_object* v_nextMacroScope_2412_; lean_object* v_ngen_2413_; lean_object* v_auxDeclNGen_2414_; lean_object* v_traceState_2415_; lean_object* v_messages_2416_; lean_object* v_infoState_2417_; lean_object* v_snapshotTasks_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2510_; 
v___x_2409_ = lean_st_ref_set(v_a_2346_, v___x_2408_);
v___x_2410_ = lean_st_ref_take(v_a_2348_);
v_env_2411_ = lean_ctor_get(v___x_2410_, 0);
v_nextMacroScope_2412_ = lean_ctor_get(v___x_2410_, 1);
v_ngen_2413_ = lean_ctor_get(v___x_2410_, 2);
v_auxDeclNGen_2414_ = lean_ctor_get(v___x_2410_, 3);
v_traceState_2415_ = lean_ctor_get(v___x_2410_, 4);
v_messages_2416_ = lean_ctor_get(v___x_2410_, 6);
v_infoState_2417_ = lean_ctor_get(v___x_2410_, 7);
v_snapshotTasks_2418_ = lean_ctor_get(v___x_2410_, 8);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v___x_2410_, 5);
lean_dec(v_unused_2511_);
v___x_2420_ = v___x_2410_;
v_isShared_2421_ = v_isSharedCheck_2510_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_snapshotTasks_2418_);
lean_inc(v_infoState_2417_);
lean_inc(v_messages_2416_);
lean_inc(v_traceState_2415_);
lean_inc(v_auxDeclNGen_2414_);
lean_inc(v_ngen_2413_);
lean_inc(v_nextMacroScope_2412_);
lean_inc(v_env_2411_);
lean_dec(v___x_2410_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2510_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_inc(v_declName_2343_);
v___x_2422_ = l_Lean_markAuxRecursor(v_env_2411_, v_declName_2343_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 5, v___x_2394_);
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_nextMacroScope_2412_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_ngen_2413_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_auxDeclNGen_2414_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_traceState_2415_);
lean_ctor_set(v_reuseFailAlloc_2509_, 5, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2509_, 6, v_messages_2416_);
lean_ctor_set(v_reuseFailAlloc_2509_, 7, v_infoState_2417_);
lean_ctor_set(v_reuseFailAlloc_2509_, 8, v_snapshotTasks_2418_);
v___x_2424_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_mctx_2427_; lean_object* v_zetaDeltaFVarIds_2428_; lean_object* v_postponed_2429_; lean_object* v_diag_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2507_; 
v___x_2425_ = lean_st_ref_set(v_a_2348_, v___x_2424_);
v___x_2426_ = lean_st_ref_take(v_a_2346_);
v_mctx_2427_ = lean_ctor_get(v___x_2426_, 0);
v_zetaDeltaFVarIds_2428_ = lean_ctor_get(v___x_2426_, 2);
v_postponed_2429_ = lean_ctor_get(v___x_2426_, 3);
v_diag_2430_ = lean_ctor_get(v___x_2426_, 4);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2426_, 1);
lean_dec(v_unused_2508_);
v___x_2432_ = v___x_2426_;
v_isShared_2433_ = v_isSharedCheck_2507_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_diag_2430_);
lean_inc(v_postponed_2429_);
lean_inc(v_zetaDeltaFVarIds_2428_);
lean_inc(v_mctx_2427_);
lean_dec(v___x_2426_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2507_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___x_2406_);
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_mctx_2427_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_zetaDeltaFVarIds_2428_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_postponed_2429_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v_diag_2430_);
v___x_2435_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_env_2438_; lean_object* v_nextMacroScope_2439_; lean_object* v_ngen_2440_; lean_object* v_auxDeclNGen_2441_; lean_object* v_traceState_2442_; lean_object* v_messages_2443_; lean_object* v_infoState_2444_; lean_object* v_snapshotTasks_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2504_; 
v___x_2436_ = lean_st_ref_set(v_a_2346_, v___x_2435_);
v___x_2437_ = lean_st_ref_take(v_a_2348_);
v_env_2438_ = lean_ctor_get(v___x_2437_, 0);
v_nextMacroScope_2439_ = lean_ctor_get(v___x_2437_, 1);
v_ngen_2440_ = lean_ctor_get(v___x_2437_, 2);
v_auxDeclNGen_2441_ = lean_ctor_get(v___x_2437_, 3);
v_traceState_2442_ = lean_ctor_get(v___x_2437_, 4);
v_messages_2443_ = lean_ctor_get(v___x_2437_, 6);
v_infoState_2444_ = lean_ctor_get(v___x_2437_, 7);
v_snapshotTasks_2445_ = lean_ctor_get(v___x_2437_, 8);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v___x_2437_, 5);
lean_dec(v_unused_2505_);
v___x_2447_ = v___x_2437_;
v_isShared_2448_ = v_isSharedCheck_2504_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_snapshotTasks_2445_);
lean_inc(v_infoState_2444_);
lean_inc(v_messages_2443_);
lean_inc(v_traceState_2442_);
lean_inc(v_auxDeclNGen_2441_);
lean_inc(v_ngen_2440_);
lean_inc(v_nextMacroScope_2439_);
lean_inc(v_env_2438_);
lean_dec(v___x_2437_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2504_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_inc(v_declName_2343_);
v___x_2449_ = l_Lean_Meta_addToCompletionBlackList(v_env_2438_, v_declName_2343_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 5, v___x_2394_);
lean_ctor_set(v___x_2447_, 0, v___x_2449_);
v___x_2451_ = v___x_2447_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_nextMacroScope_2439_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_ngen_2440_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_auxDeclNGen_2441_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_traceState_2442_);
lean_ctor_set(v_reuseFailAlloc_2503_, 5, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2503_, 6, v_messages_2443_);
lean_ctor_set(v_reuseFailAlloc_2503_, 7, v_infoState_2444_);
lean_ctor_set(v_reuseFailAlloc_2503_, 8, v_snapshotTasks_2445_);
v___x_2451_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_mctx_2454_; lean_object* v_zetaDeltaFVarIds_2455_; lean_object* v_postponed_2456_; lean_object* v_diag_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2501_; 
v___x_2452_ = lean_st_ref_set(v_a_2348_, v___x_2451_);
v___x_2453_ = lean_st_ref_take(v_a_2346_);
v_mctx_2454_ = lean_ctor_get(v___x_2453_, 0);
v_zetaDeltaFVarIds_2455_ = lean_ctor_get(v___x_2453_, 2);
v_postponed_2456_ = lean_ctor_get(v___x_2453_, 3);
v_diag_2457_ = lean_ctor_get(v___x_2453_, 4);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2453_, 1);
lean_dec(v_unused_2502_);
v___x_2459_ = v___x_2453_;
v_isShared_2460_ = v_isSharedCheck_2501_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_diag_2457_);
lean_inc(v_postponed_2456_);
lean_inc(v_zetaDeltaFVarIds_2455_);
lean_inc(v_mctx_2454_);
lean_dec(v___x_2453_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2501_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2406_);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_mctx_2454_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_zetaDeltaFVarIds_2455_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_postponed_2456_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v_diag_2457_);
v___x_2462_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_env_2465_; lean_object* v_nextMacroScope_2466_; lean_object* v_ngen_2467_; lean_object* v_auxDeclNGen_2468_; lean_object* v_traceState_2469_; lean_object* v_messages_2470_; lean_object* v_infoState_2471_; lean_object* v_snapshotTasks_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2498_; 
v___x_2463_ = lean_st_ref_set(v_a_2346_, v___x_2462_);
v___x_2464_ = lean_st_ref_take(v_a_2348_);
v_env_2465_ = lean_ctor_get(v___x_2464_, 0);
v_nextMacroScope_2466_ = lean_ctor_get(v___x_2464_, 1);
v_ngen_2467_ = lean_ctor_get(v___x_2464_, 2);
v_auxDeclNGen_2468_ = lean_ctor_get(v___x_2464_, 3);
v_traceState_2469_ = lean_ctor_get(v___x_2464_, 4);
v_messages_2470_ = lean_ctor_get(v___x_2464_, 6);
v_infoState_2471_ = lean_ctor_get(v___x_2464_, 7);
v_snapshotTasks_2472_ = lean_ctor_get(v___x_2464_, 8);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2464_, 5);
lean_dec(v_unused_2499_);
v___x_2474_ = v___x_2464_;
v_isShared_2475_ = v_isSharedCheck_2498_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_snapshotTasks_2472_);
lean_inc(v_infoState_2471_);
lean_inc(v_messages_2470_);
lean_inc(v_traceState_2469_);
lean_inc(v_auxDeclNGen_2468_);
lean_inc(v_ngen_2467_);
lean_inc(v_nextMacroScope_2466_);
lean_inc(v_env_2465_);
lean_dec(v___x_2464_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2498_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_inc(v_declName_2343_);
v___x_2476_ = l_Lean_addProtected(v_env_2465_, v_declName_2343_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 5, v___x_2394_);
lean_ctor_set(v___x_2474_, 0, v___x_2476_);
v___x_2478_ = v___x_2474_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_nextMacroScope_2466_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_ngen_2467_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_auxDeclNGen_2468_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_traceState_2469_);
lean_ctor_set(v_reuseFailAlloc_2497_, 5, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2497_, 6, v_messages_2470_);
lean_ctor_set(v_reuseFailAlloc_2497_, 7, v_infoState_2471_);
lean_ctor_set(v_reuseFailAlloc_2497_, 8, v_snapshotTasks_2472_);
v___x_2478_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v_mctx_2481_; lean_object* v_zetaDeltaFVarIds_2482_; lean_object* v_postponed_2483_; lean_object* v_diag_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2495_; 
v___x_2479_ = lean_st_ref_set(v_a_2348_, v___x_2478_);
v___x_2480_ = lean_st_ref_take(v_a_2346_);
v_mctx_2481_ = lean_ctor_get(v___x_2480_, 0);
v_zetaDeltaFVarIds_2482_ = lean_ctor_get(v___x_2480_, 2);
v_postponed_2483_ = lean_ctor_get(v___x_2480_, 3);
v_diag_2484_ = lean_ctor_get(v___x_2480_, 4);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2480_, 1);
lean_dec(v_unused_2496_);
v___x_2486_ = v___x_2480_;
v_isShared_2487_ = v_isSharedCheck_2495_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_diag_2484_);
lean_inc(v_postponed_2483_);
lean_inc(v_zetaDeltaFVarIds_2482_);
lean_inc(v_mctx_2481_);
lean_dec(v___x_2480_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2495_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___x_2406_);
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_mctx_2481_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_zetaDeltaFVarIds_2482_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_postponed_2483_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_diag_2484_);
v___x_2489_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_st_ref_set(v_a_2346_, v___x_2489_);
v___x_2491_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2343_);
v___x_2492_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2491_, v_declName_2343_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v___x_2493_; 
lean_dec_ref(v___x_2492_);
v___x_2493_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2343_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
return v___x_2493_;
}
else
{
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_declName_2343_);
return v___x_2492_;
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
}
}
}
}
}
}
else
{
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_declName_2343_);
return v___x_2380_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_levelParams_2360_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_declName_2343_);
v_a_2520_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2374_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2374_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v___x_2363_);
lean_dec_ref(v_type_2361_);
lean_dec(v_levelParams_2360_);
lean_dec(v_name_2359_);
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_val_2352_);
lean_dec(v_indName_2344_);
lean_dec(v_declName_2343_);
v___x_2529_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2530_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2529_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
return v___x_2530_;
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_val_2352_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_indName_2344_);
lean_dec(v_declName_2343_);
v_a_2531_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2357_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2357_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec(v_a_2351_);
lean_dec(v_indName_2344_);
lean_dec(v_declName_2343_);
v___x_2540_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2541_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2540_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
return v___x_2541_;
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_indName_2344_);
lean_dec(v_declName_2343_);
v_a_2542_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2350_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2350_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2550_, lean_object* v_indName_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2550_, v_indName_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2558_, lean_object* v_name_2559_, lean_object* v_type_2560_, lean_object* v_k_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2559_, v_type_2560_, v_k_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_name_2569_, lean_object* v_type_2570_, lean_object* v_k_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2568_, v_name_2569_, v_type_2570_, v_k_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2578_, lean_object* v_params_2579_, lean_object* v_alts_2580_, lean_object* v___x_2581_, lean_object* v_ism2_2582_, lean_object* v_motive_2583_, lean_object* v_val_2584_, lean_object* v_indName_2585_, lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v_as_2589_, lean_object* v_i_2590_, lean_object* v_j_2591_, lean_object* v_inv_2592_, lean_object* v_bs_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2578_, v_params_2579_, v_alts_2580_, v___x_2581_, v_ism2_2582_, v_motive_2583_, v_val_2584_, v_indName_2585_, v___x_2586_, v___x_2587_, v___x_2588_, v_as_2589_, v_i_2590_, v_j_2591_, v_bs_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2600_ = _args[0];
lean_object* v_params_2601_ = _args[1];
lean_object* v_alts_2602_ = _args[2];
lean_object* v___x_2603_ = _args[3];
lean_object* v_ism2_2604_ = _args[4];
lean_object* v_motive_2605_ = _args[5];
lean_object* v_val_2606_ = _args[6];
lean_object* v_indName_2607_ = _args[7];
lean_object* v___x_2608_ = _args[8];
lean_object* v___x_2609_ = _args[9];
lean_object* v___x_2610_ = _args[10];
lean_object* v_as_2611_ = _args[11];
lean_object* v_i_2612_ = _args[12];
lean_object* v_j_2613_ = _args[13];
lean_object* v_inv_2614_ = _args[14];
lean_object* v_bs_2615_ = _args[15];
lean_object* v___y_2616_ = _args[16];
lean_object* v___y_2617_ = _args[17];
lean_object* v___y_2618_ = _args[18];
lean_object* v___y_2619_ = _args[19];
lean_object* v___y_2620_ = _args[20];
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2600_, v_params_2601_, v_alts_2602_, v___x_2603_, v_ism2_2604_, v_motive_2605_, v_val_2606_, v_indName_2607_, v___x_2608_, v___x_2609_, v___x_2610_, v_as_2611_, v_i_2612_, v_j_2613_, v_inv_2614_, v_bs_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec_ref(v_as_2611_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2622_, lean_object* v_params_2623_, lean_object* v___x_2624_, lean_object* v_motive_2625_, lean_object* v_as_2626_, lean_object* v_i_2627_, lean_object* v_j_2628_, lean_object* v_inv_2629_, lean_object* v_bs_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2622_, v_params_2623_, v___x_2624_, v_motive_2625_, v_as_2626_, v_i_2627_, v_j_2628_, v_bs_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2637_, lean_object* v_params_2638_, lean_object* v___x_2639_, lean_object* v_motive_2640_, lean_object* v_as_2641_, lean_object* v_i_2642_, lean_object* v_j_2643_, lean_object* v_inv_2644_, lean_object* v_bs_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2637_, v_params_2638_, v___x_2639_, v_motive_2640_, v_as_2641_, v_i_2642_, v_j_2643_, v_inv_2644_, v_bs_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v_as_2641_);
lean_dec_ref(v_params_2638_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_00_u03b1_2652_, lean_object* v_inst_2653_, lean_object* v_declInfos_2654_, lean_object* v_k_2655_, uint8_t v_kind_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v_inst_2653_, v_declInfos_2654_, v_k_2655_, v_kind_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_00_u03b1_2663_, lean_object* v_inst_2664_, lean_object* v_declInfos_2665_, lean_object* v_k_2666_, lean_object* v_kind_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v_kind_boxed_2673_; lean_object* v_res_2674_; 
v_kind_boxed_2673_ = lean_unbox(v_kind_2667_);
v_res_2674_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_00_u03b1_2663_, v_inst_2664_, v_declInfos_2665_, v_k_2666_, v_kind_boxed_2673_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v_inst_2664_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2675_, uint8_t v_s_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2675_, v_s_2676_, v___y_2678_, v___y_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2683_, lean_object* v_s_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
uint8_t v_s_boxed_2690_; lean_object* v_res_2691_; 
v_s_boxed_2690_ = lean_unbox(v_s_2684_);
v_res_2691_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2683_, v_s_boxed_2690_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2692_, lean_object* v_constName_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2700_, lean_object* v_constName_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2700_, v_constName_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_00_u03b1_2708_, lean_object* v_inst_2709_, lean_object* v_declInfos_2710_, lean_object* v_k_2711_, uint8_t v_kind_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(v_inst_2709_, v_declInfos_2710_, v_k_2711_, v_kind_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_inst_2720_, lean_object* v_declInfos_2721_, lean_object* v_k_2722_, lean_object* v_kind_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v_kind_boxed_2729_; lean_object* v_res_2730_; 
v_kind_boxed_2729_ = lean_unbox(v_kind_2723_);
v_res_2730_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_00_u03b1_2719_, v_inst_2720_, v_declInfos_2721_, v_k_2722_, v_kind_boxed_2729_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v_inst_2720_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2731_, lean_object* v_attrName_2732_, lean_object* v_declName_2733_, lean_object* v_asyncPrefix_x3f_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2732_, v_declName_2733_, v_asyncPrefix_x3f_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_attrName_2742_, lean_object* v_declName_2743_, lean_object* v_asyncPrefix_x3f_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2741_, v_attrName_2742_, v_declName_2743_, v_asyncPrefix_x3f_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2751_, lean_object* v_attrName_2752_, lean_object* v_declName_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2752_, v_declName_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_attrName_2761_, lean_object* v_declName_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2760_, v_attrName_2761_, v_declName_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2769_, lean_object* v_ref_2770_, lean_object* v_constName_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2770_, v_constName_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_ref_2779_, lean_object* v_constName_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2778_, v_ref_2779_, v_constName_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v_ref_2779_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_00_u03b1_2787_, lean_object* v_inst_2788_, lean_object* v_declInfos_2789_, lean_object* v_k_2790_, uint8_t v_kind_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(v_inst_2788_, v_declInfos_2789_, v_k_2790_, v_kind_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_inst_2799_, lean_object* v_declInfos_2800_, lean_object* v_k_2801_, lean_object* v_kind_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v_kind_boxed_2808_; lean_object* v_res_2809_; 
v_kind_boxed_2808_ = lean_unbox(v_kind_2802_);
v_res_2809_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_00_u03b1_2798_, v_inst_2799_, v_declInfos_2800_, v_k_2801_, v_kind_boxed_2808_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v_inst_2799_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2810_, lean_object* v_msg_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2818_, lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2818_, v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2826_, lean_object* v_ref_2827_, lean_object* v_msg_2828_, lean_object* v_declHint_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2827_, v_msg_2828_, v_declHint_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_ref_2837_, lean_object* v_msg_2838_, lean_object* v_declHint_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2836_, v_ref_2837_, v_msg_2838_, v_declHint_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v_ref_2837_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_00_u03b1_2846_, lean_object* v_declInfos_2847_, lean_object* v_k_2848_, uint8_t v_kind_2849_, lean_object* v_inst_2850_, lean_object* v_acc_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_2847_, v_k_2848_, v_kind_2849_, v_acc_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_declInfos_2859_, lean_object* v_k_2860_, lean_object* v_kind_2861_, lean_object* v_inst_2862_, lean_object* v_acc_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
uint8_t v_kind_boxed_2869_; lean_object* v_res_2870_; 
v_kind_boxed_2869_ = lean_unbox(v_kind_2861_);
v_res_2870_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_00_u03b1_2858_, v_declInfos_2859_, v_k_2860_, v_kind_boxed_2869_, v_inst_2862_, v_acc_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v_inst_2862_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2871_, lean_object* v_declHint_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2871_, v_declHint_2872_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2879_, lean_object* v_declHint_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2879_, v_declHint_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2887_, lean_object* v_ref_2888_, lean_object* v_msg_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2888_, v_msg_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2896_, lean_object* v_ref_2897_, lean_object* v_msg_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2896_, v_ref_2897_, v_msg_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v_ref_2897_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2905_, lean_object* v___y_2906_){
_start:
{
uint8_t v___x_2908_; 
v___x_2908_ = l_Lean_Expr_hasMVar(v_e_2905_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_e_2905_);
return v___x_2909_;
}
else
{
lean_object* v___x_2910_; lean_object* v_mctx_2911_; lean_object* v___x_2912_; lean_object* v_fst_2913_; lean_object* v_snd_2914_; lean_object* v___x_2915_; lean_object* v_cache_2916_; lean_object* v_zetaDeltaFVarIds_2917_; lean_object* v_postponed_2918_; lean_object* v_diag_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2928_; 
v___x_2910_ = lean_st_ref_get(v___y_2906_);
v_mctx_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc_ref(v_mctx_2911_);
lean_dec(v___x_2910_);
v___x_2912_ = l_Lean_instantiateMVarsCore(v_mctx_2911_, v_e_2905_);
v_fst_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_fst_2913_);
v_snd_2914_ = lean_ctor_get(v___x_2912_, 1);
lean_inc(v_snd_2914_);
lean_dec_ref(v___x_2912_);
v___x_2915_ = lean_st_ref_take(v___y_2906_);
v_cache_2916_ = lean_ctor_get(v___x_2915_, 1);
v_zetaDeltaFVarIds_2917_ = lean_ctor_get(v___x_2915_, 2);
v_postponed_2918_ = lean_ctor_get(v___x_2915_, 3);
v_diag_2919_ = lean_ctor_get(v___x_2915_, 4);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v___x_2915_, 0);
lean_dec(v_unused_2929_);
v___x_2921_ = v___x_2915_;
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_diag_2919_);
lean_inc(v_postponed_2918_);
lean_inc(v_zetaDeltaFVarIds_2917_);
lean_inc(v_cache_2916_);
lean_dec(v___x_2915_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2928_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v_snd_2914_);
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_snd_2914_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_cache_2916_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_zetaDeltaFVarIds_2917_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_postponed_2918_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_diag_2919_);
v___x_2924_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_st_ref_set(v___y_2906_, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_fst_2913_);
return v___x_2926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2930_, v___y_2931_);
lean_dec(v___y_2931_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2934_, v___y_2936_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2948_, lean_object* v_info_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; lean_object* v_env_2954_; lean_object* v_nextMacroScope_2955_; lean_object* v_ngen_2956_; lean_object* v_auxDeclNGen_2957_; lean_object* v_traceState_2958_; lean_object* v_messages_2959_; lean_object* v_infoState_2960_; lean_object* v_snapshotTasks_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2988_; 
v___x_2953_ = lean_st_ref_take(v___y_2951_);
v_env_2954_ = lean_ctor_get(v___x_2953_, 0);
v_nextMacroScope_2955_ = lean_ctor_get(v___x_2953_, 1);
v_ngen_2956_ = lean_ctor_get(v___x_2953_, 2);
v_auxDeclNGen_2957_ = lean_ctor_get(v___x_2953_, 3);
v_traceState_2958_ = lean_ctor_get(v___x_2953_, 4);
v_messages_2959_ = lean_ctor_get(v___x_2953_, 6);
v_infoState_2960_ = lean_ctor_get(v___x_2953_, 7);
v_snapshotTasks_2961_ = lean_ctor_get(v___x_2953_, 8);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2953_, 5);
lean_dec(v_unused_2989_);
v___x_2963_ = v___x_2953_;
v_isShared_2964_ = v_isSharedCheck_2988_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snapshotTasks_2961_);
lean_inc(v_infoState_2960_);
lean_inc(v_messages_2959_);
lean_inc(v_traceState_2958_);
lean_inc(v_auxDeclNGen_2957_);
lean_inc(v_ngen_2956_);
lean_inc(v_nextMacroScope_2955_);
lean_inc(v_env_2954_);
lean_dec(v___x_2953_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2988_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2965_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2954_, v_matcherName_2948_, v_info_2949_);
v___x_2966_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 5, v___x_2966_);
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_nextMacroScope_2955_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_ngen_2956_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_auxDeclNGen_2957_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_traceState_2958_);
lean_ctor_set(v_reuseFailAlloc_2987_, 5, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2987_, 6, v_messages_2959_);
lean_ctor_set(v_reuseFailAlloc_2987_, 7, v_infoState_2960_);
lean_ctor_set(v_reuseFailAlloc_2987_, 8, v_snapshotTasks_2961_);
v___x_2968_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_mctx_2971_; lean_object* v_zetaDeltaFVarIds_2972_; lean_object* v_postponed_2973_; lean_object* v_diag_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2985_; 
v___x_2969_ = lean_st_ref_set(v___y_2951_, v___x_2968_);
v___x_2970_ = lean_st_ref_take(v___y_2950_);
v_mctx_2971_ = lean_ctor_get(v___x_2970_, 0);
v_zetaDeltaFVarIds_2972_ = lean_ctor_get(v___x_2970_, 2);
v_postponed_2973_ = lean_ctor_get(v___x_2970_, 3);
v_diag_2974_ = lean_ctor_get(v___x_2970_, 4);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v___x_2970_, 1);
lean_dec(v_unused_2986_);
v___x_2976_ = v___x_2970_;
v_isShared_2977_ = v_isSharedCheck_2985_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_diag_2974_);
lean_inc(v_postponed_2973_);
lean_inc(v_zetaDeltaFVarIds_2972_);
lean_inc(v_mctx_2971_);
lean_dec(v___x_2970_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2985_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_mctx_2971_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_zetaDeltaFVarIds_2972_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_postponed_2973_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_diag_2974_);
v___x_2980_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = lean_st_ref_set(v___y_2950_, v___x_2980_);
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
return v___x_2983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2990_, lean_object* v_info_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2990_, v_info_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2996_, lean_object* v_info_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2996_, v_info_2997_, v___y_2999_, v___y_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_3004_, lean_object* v_info_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_3004_, v_info_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_3012_, lean_object* v___x_3013_, lean_object* v_newEqs1_3014_, uint8_t v___x_3015_, uint8_t v___x_3016_, uint8_t v___x_3017_, lean_object* v_ism1_x27_3018_, lean_object* v_ism2_x27_3019_, lean_object* v_newRefls1_3020_, lean_object* v_newEqs2_3021_, lean_object* v_newRefls2_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = l_Lean_mkAppN(v_motive_3012_, v___x_3013_);
v___x_3029_ = l_Array_append___redArg(v_newEqs1_3014_, v_newEqs2_3021_);
v___x_3030_ = l_Lean_Meta_mkForallFVars(v___x_3029_, v___x_3028_, v___x_3015_, v___x_3016_, v___x_3016_, v___x_3017_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec_ref(v___x_3029_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = l_Array_append___redArg(v_ism1_x27_3018_, v_ism2_x27_3019_);
v___x_3033_ = l_Lean_Meta_mkLambdaFVars(v___x_3032_, v_a_3031_, v___x_3015_, v___x_3016_, v___x_3015_, v___x_3016_, v___x_3017_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec_ref(v___x_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3043_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3043_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3043_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3038_ = l_Array_append___redArg(v_newRefls1_3020_, v_newRefls2_3022_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3034_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3039_);
v___x_3041_ = v___x_3036_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v_newRefls1_3020_);
v_a_3044_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3033_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3033_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v_newRefls1_3020_);
lean_dec_ref(v_ism1_x27_3018_);
v_a_3052_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3030_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3030_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_3060_, lean_object* v___x_3061_, lean_object* v_newEqs1_3062_, lean_object* v___x_3063_, lean_object* v___x_3064_, lean_object* v___x_3065_, lean_object* v_ism1_x27_3066_, lean_object* v_ism2_x27_3067_, lean_object* v_newRefls1_3068_, lean_object* v_newEqs2_3069_, lean_object* v_newRefls2_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v___x_15192__boxed_3076_; uint8_t v___x_15193__boxed_3077_; uint8_t v___x_15194__boxed_3078_; lean_object* v_res_3079_; 
v___x_15192__boxed_3076_ = lean_unbox(v___x_3063_);
v___x_15193__boxed_3077_ = lean_unbox(v___x_3064_);
v___x_15194__boxed_3078_ = lean_unbox(v___x_3065_);
v_res_3079_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_3060_, v___x_3061_, v_newEqs1_3062_, v___x_15192__boxed_3076_, v___x_15193__boxed_3077_, v___x_15194__boxed_3078_, v_ism1_x27_3066_, v_ism2_x27_3067_, v_newRefls1_3068_, v_newEqs2_3069_, v_newRefls2_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v_newRefls2_3070_);
lean_dec_ref(v_newEqs2_3069_);
lean_dec_ref(v_ism2_x27_3067_);
lean_dec_ref(v___x_3061_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_3080_, lean_object* v___x_3081_, uint8_t v___x_3082_, uint8_t v___x_3083_, uint8_t v___x_3084_, lean_object* v_ism1_x27_3085_, lean_object* v_ism2_x27_3086_, lean_object* v_is_3087_, lean_object* v___x_3088_, lean_object* v_newEqs1_3089_, lean_object* v_newRefls1_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3096_ = lean_box(v___x_3082_);
v___x_3097_ = lean_box(v___x_3083_);
v___x_3098_ = lean_box(v___x_3084_);
lean_inc_ref(v_ism2_x27_3086_);
v___f_3099_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3099_, 0, v_motive_3080_);
lean_closure_set(v___f_3099_, 1, v___x_3081_);
lean_closure_set(v___f_3099_, 2, v_newEqs1_3089_);
lean_closure_set(v___f_3099_, 3, v___x_3096_);
lean_closure_set(v___f_3099_, 4, v___x_3097_);
lean_closure_set(v___f_3099_, 5, v___x_3098_);
lean_closure_set(v___f_3099_, 6, v_ism1_x27_3085_);
lean_closure_set(v___f_3099_, 7, v_ism2_x27_3086_);
lean_closure_set(v___f_3099_, 8, v_newRefls1_3090_);
v___x_3100_ = lean_array_push(v_is_3087_, v___x_3088_);
v___x_3101_ = l_Lean_Meta_withNewEqs___redArg(v___x_3100_, v_ism2_x27_3086_, v___f_3099_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_3102_, lean_object* v___x_3103_, lean_object* v___x_3104_, lean_object* v___x_3105_, lean_object* v___x_3106_, lean_object* v_ism1_x27_3107_, lean_object* v_ism2_x27_3108_, lean_object* v_is_3109_, lean_object* v___x_3110_, lean_object* v_newEqs1_3111_, lean_object* v_newRefls1_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v___x_15283__boxed_3118_; uint8_t v___x_15284__boxed_3119_; uint8_t v___x_15285__boxed_3120_; lean_object* v_res_3121_; 
v___x_15283__boxed_3118_ = lean_unbox(v___x_3104_);
v___x_15284__boxed_3119_ = lean_unbox(v___x_3105_);
v___x_15285__boxed_3120_ = lean_unbox(v___x_3106_);
v_res_3121_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3102_, v___x_3103_, v___x_15283__boxed_3118_, v___x_15284__boxed_3119_, v___x_15285__boxed_3120_, v_ism1_x27_3107_, v_ism2_x27_3108_, v_is_3109_, v___x_3110_, v_newEqs1_3111_, v_newRefls1_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3122_, uint8_t v___x_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_addDecl(v___x_3122_, v___x_3123_, v___y_3126_, v___y_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v___x_15325__boxed_3137_; lean_object* v_res_3138_; 
v___x_15325__boxed_3137_ = lean_unbox(v___x_3131_);
v_res_3138_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3130_, v___x_15325__boxed_3137_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3138_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3144_ = l_Lean_stringToMessageData(v___x_3143_);
return v___x_3144_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = lean_box(0);
v___x_3151_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3152_ = l_Lean_mkConst(v___x_3151_, v___x_3150_);
return v___x_3152_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3156_, lean_object* v_a_3157_, lean_object* v_j_3158_, lean_object* v_zs1_3159_, lean_object* v_snd_3160_, uint8_t v___x_3161_, uint8_t v_isZero_3162_, uint8_t v___x_3163_, lean_object* v_alts_3164_, lean_object* v_zs2_3165_, lean_object* v___ctorRet2_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_inc_ref(v___x_3156_);
v___x_3172_ = lean_array_get_borrowed(v___x_3156_, v_a_3157_, v_j_3158_);
lean_inc_ref(v_zs1_3159_);
v___x_3173_ = l_Array_append___redArg(v_zs1_3159_, v_zs2_3165_);
lean_inc(v___y_3170_);
lean_inc_ref(v___y_3169_);
lean_inc(v___y_3168_);
lean_inc_ref(v___y_3167_);
lean_inc(v___x_3172_);
v___x_3174_ = l_Lean_Meta_instantiateForall(v___x_3172_, v___x_3173_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v___x_3176_ = lean_box(0);
lean_inc_ref(v___y_3167_);
v___x_3177_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3175_, v___x_3176_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
v___x_3179_ = l_Lean_Expr_mvarId_x21(v_a_3178_);
v___x_3180_ = lean_array_get_size(v_snd_3160_);
v___x_3181_ = lean_box(0);
v___x_3182_ = lean_box(0);
lean_inc(v___y_3170_);
lean_inc_ref(v___y_3169_);
lean_inc(v___y_3168_);
lean_inc_ref(v___y_3167_);
v___x_3183_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3180_, v___x_3179_, v___x_3181_, v___x_3182_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3183_);
if (lean_obj_tag(v_a_3184_) == 1)
{
lean_object* v_val_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3232_; 
v_val_3185_ = lean_ctor_get(v_a_3184_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_a_3184_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3187_ = v_a_3184_;
v_isShared_3188_ = v_isSharedCheck_3232_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_val_3185_);
lean_dec(v_a_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3232_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_fst_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3230_; 
v_fst_3189_ = lean_ctor_get(v_val_3185_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_val_3185_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v_val_3185_, 1);
lean_dec(v_unused_3231_);
v___x_3191_ = v_val_3185_;
v_isShared_3192_ = v_isSharedCheck_3230_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_fst_3189_);
lean_dec(v_val_3185_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3230_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___y_3194_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3222_ = lean_array_get_borrowed(v___x_3156_, v_alts_3164_, v_j_3158_);
v___x_3223_ = lean_array_get_size(v_zs1_3159_);
lean_dec_ref(v_zs1_3159_);
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = lean_nat_dec_eq(v___x_3223_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_inc(v___x_3222_);
v___y_3194_ = v___x_3222_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3226_ = lean_array_get_size(v_zs2_3165_);
v___x_3227_ = lean_nat_dec_eq(v___x_3226_, v___x_3224_);
if (v___x_3227_ == 0)
{
lean_inc(v___x_3222_);
v___y_3194_ = v___x_3222_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3222_);
v___x_3229_ = l_Lean_Expr_app___override(v___x_3222_, v___x_3228_);
v___y_3194_ = v___x_3229_;
goto v___jp_3193_;
}
}
v___jp_3193_:
{
uint8_t v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = 0;
v___x_3196_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3196_, 0, v___x_3195_);
lean_ctor_set_uint8(v___x_3196_, 1, v___x_3161_);
lean_ctor_set_uint8(v___x_3196_, 2, v_isZero_3162_);
lean_ctor_set_uint8(v___x_3196_, 3, v___x_3161_);
lean_inc(v___y_3170_);
lean_inc_ref(v___y_3169_);
lean_inc(v___y_3168_);
lean_inc_ref(v___y_3167_);
lean_inc_ref(v___y_3194_);
lean_inc(v_fst_3189_);
v___x_3197_ = l_Lean_MVarId_apply(v_fst_3189_, v___y_3194_, v___x_3196_, v___x_3182_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3197_);
if (lean_obj_tag(v_a_3198_) == 0)
{
lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3201_; 
lean_dec_ref(v___y_3194_);
lean_del_object(v___x_3191_);
lean_dec(v_fst_3189_);
lean_del_object(v___x_3187_);
v___x_3199_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3178_, v___y_3168_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref(v___x_3199_);
v___x_3201_ = l_Lean_Meta_mkLambdaFVars(v___x_3173_, v_a_3200_, v_isZero_3162_, v___x_3161_, v_isZero_3162_, v___x_3161_, v___x_3163_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec_ref(v___x_3173_);
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_dec(v_a_3198_);
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3173_);
v___x_3202_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3203_ = l_Lean_MessageData_ofExpr(v___y_3194_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set_tag(v___x_3191_, 7);
lean_ctor_set(v___x_3191_, 1, v___x_3203_);
lean_ctor_set(v___x_3191_, 0, v___x_3202_);
v___x_3205_ = v___x_3191_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3206_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v_fst_3189_);
v___x_3209_ = v___x_3187_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_fst_3189_);
v___x_3209_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3207_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3210_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___y_3194_);
lean_del_object(v___x_3191_);
lean_dec(v_fst_3189_);
lean_del_object(v___x_3187_);
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3173_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
v_a_3214_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3197_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3197_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_dec(v_a_3184_);
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3173_);
lean_dec_ref(v_zs1_3159_);
lean_dec_ref(v___x_3156_);
v___x_3233_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3234_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3233_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v___x_3234_;
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3173_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec_ref(v_zs1_3159_);
lean_dec_ref(v___x_3156_);
v_a_3235_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3183_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3183_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_dec_ref(v___x_3173_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec_ref(v_zs1_3159_);
lean_dec_ref(v___x_3156_);
return v___x_3177_;
}
}
else
{
lean_dec_ref(v___x_3173_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec_ref(v_zs1_3159_);
lean_dec_ref(v___x_3156_);
return v___x_3174_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3243_, lean_object* v_a_3244_, lean_object* v_j_3245_, lean_object* v_zs1_3246_, lean_object* v_snd_3247_, lean_object* v___x_3248_, lean_object* v_isZero_3249_, lean_object* v___x_3250_, lean_object* v_alts_3251_, lean_object* v_zs2_3252_, lean_object* v___ctorRet2_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v___x_15384__boxed_3259_; uint8_t v_isZero_boxed_3260_; uint8_t v___x_15385__boxed_3261_; lean_object* v_res_3262_; 
v___x_15384__boxed_3259_ = lean_unbox(v___x_3248_);
v_isZero_boxed_3260_ = lean_unbox(v_isZero_3249_);
v___x_15385__boxed_3261_ = lean_unbox(v___x_3250_);
v_res_3262_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3243_, v_a_3244_, v_j_3245_, v_zs1_3246_, v_snd_3247_, v___x_15384__boxed_3259_, v_isZero_boxed_3260_, v___x_15385__boxed_3261_, v_alts_3251_, v_zs2_3252_, v___ctorRet2_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec_ref(v___ctorRet2_3253_);
lean_dec_ref(v_zs2_3252_);
lean_dec_ref(v_alts_3251_);
lean_dec_ref(v_snd_3247_);
lean_dec(v_j_3245_);
lean_dec_ref(v_a_3244_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3263_, lean_object* v_a_3264_, lean_object* v_j_3265_, lean_object* v_snd_3266_, uint8_t v___x_3267_, uint8_t v_isZero_3268_, uint8_t v___x_3269_, lean_object* v_alts_3270_, lean_object* v_a_3271_, lean_object* v_zs1_3272_, lean_object* v___ctorRet1_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; 
v___x_3279_ = lean_box(v___x_3267_);
v___x_3280_ = lean_box(v_isZero_3268_);
v___x_3281_ = lean_box(v___x_3269_);
v___f_3282_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3282_, 0, v___x_3263_);
lean_closure_set(v___f_3282_, 1, v_a_3264_);
lean_closure_set(v___f_3282_, 2, v_j_3265_);
lean_closure_set(v___f_3282_, 3, v_zs1_3272_);
lean_closure_set(v___f_3282_, 4, v_snd_3266_);
lean_closure_set(v___f_3282_, 5, v___x_3279_);
lean_closure_set(v___f_3282_, 6, v___x_3280_);
lean_closure_set(v___f_3282_, 7, v___x_3281_);
lean_closure_set(v___f_3282_, 8, v_alts_3270_);
v___x_3283_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3271_, v___f_3282_, v_isZero_3268_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3284_, lean_object* v_a_3285_, lean_object* v_j_3286_, lean_object* v_snd_3287_, lean_object* v___x_3288_, lean_object* v_isZero_3289_, lean_object* v___x_3290_, lean_object* v_alts_3291_, lean_object* v_a_3292_, lean_object* v_zs1_3293_, lean_object* v___ctorRet1_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
uint8_t v___x_15577__boxed_3300_; uint8_t v_isZero_boxed_3301_; uint8_t v___x_15578__boxed_3302_; lean_object* v_res_3303_; 
v___x_15577__boxed_3300_ = lean_unbox(v___x_3288_);
v_isZero_boxed_3301_ = lean_unbox(v_isZero_3289_);
v___x_15578__boxed_3302_ = lean_unbox(v___x_3290_);
v_res_3303_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3284_, v_a_3285_, v_j_3286_, v_snd_3287_, v___x_15577__boxed_3300_, v_isZero_boxed_3301_, v___x_15578__boxed_3302_, v_alts_3291_, v_a_3292_, v_zs1_3293_, v___ctorRet1_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec_ref(v___ctorRet1_3294_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3304_, lean_object* v_params_3305_, lean_object* v_a_3306_, lean_object* v_snd_3307_, lean_object* v_alts_3308_, lean_object* v_as_3309_, lean_object* v_i_3310_, lean_object* v_j_3311_, lean_object* v_bs_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_zero_3318_; uint8_t v_isZero_3319_; 
v_zero_3318_ = lean_unsigned_to_nat(0u);
v_isZero_3319_ = lean_nat_dec_eq(v_i_3310_, v_zero_3318_);
if (v_isZero_3319_ == 1)
{
lean_object* v___x_3320_; 
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v_j_3311_);
lean_dec(v_i_3310_);
lean_dec_ref(v_alts_3308_);
lean_dec_ref(v_snd_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_tail_3304_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_bs_3312_);
return v___x_3320_;
}
else
{
lean_object* v_one_3321_; lean_object* v_n_3322_; lean_object* v___y_3324_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_one_3321_ = lean_unsigned_to_nat(1u);
v_n_3322_ = lean_nat_sub(v_i_3310_, v_one_3321_);
lean_dec(v_i_3310_);
v___x_3337_ = lean_array_fget_borrowed(v_as_3309_, v_j_3311_);
lean_inc(v_tail_3304_);
lean_inc(v___x_3337_);
v___x_3338_ = l_Lean_mkConst(v___x_3337_, v_tail_3304_);
v___x_3339_ = l_Lean_mkAppN(v___x_3338_, v_params_3305_);
lean_inc(v___y_3316_);
lean_inc_ref(v___y_3315_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
v___x_3340_ = lean_infer_type(v___x_3339_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = l_Lean_instInhabitedExpr;
v___x_3343_ = 1;
v___x_3344_ = 1;
v___x_3345_ = lean_box(v___x_3343_);
v___x_3346_ = lean_box(v_isZero_3319_);
v___x_3347_ = lean_box(v___x_3344_);
lean_inc(v_a_3341_);
lean_inc_ref(v_alts_3308_);
lean_inc_ref(v_snd_3307_);
lean_inc(v_j_3311_);
lean_inc_ref(v_a_3306_);
v___f_3348_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3348_, 0, v___x_3342_);
lean_closure_set(v___f_3348_, 1, v_a_3306_);
lean_closure_set(v___f_3348_, 2, v_j_3311_);
lean_closure_set(v___f_3348_, 3, v_snd_3307_);
lean_closure_set(v___f_3348_, 4, v___x_3345_);
lean_closure_set(v___f_3348_, 5, v___x_3346_);
lean_closure_set(v___f_3348_, 6, v___x_3347_);
lean_closure_set(v___f_3348_, 7, v_alts_3308_);
lean_closure_set(v___f_3348_, 8, v_a_3341_);
lean_inc(v___y_3316_);
lean_inc_ref(v___y_3315_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
v___x_3349_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3341_, v___f_3348_, v_isZero_3319_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
v___y_3324_ = v___x_3349_;
goto v___jp_3323_;
}
else
{
v___y_3324_ = v___x_3340_;
goto v___jp_3323_;
}
v___jp_3323_:
{
if (lean_obj_tag(v___y_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_a_3325_ = lean_ctor_get(v___y_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___y_3324_);
v___x_3326_ = lean_nat_add(v_j_3311_, v_one_3321_);
lean_dec(v_j_3311_);
v___x_3327_ = lean_array_push(v_bs_3312_, v_a_3325_);
v_i_3310_ = v_n_3322_;
v_j_3311_ = v___x_3326_;
v_bs_3312_ = v___x_3327_;
goto _start;
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec(v_n_3322_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec_ref(v_bs_3312_);
lean_dec(v_j_3311_);
lean_dec_ref(v_alts_3308_);
lean_dec_ref(v_snd_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_tail_3304_);
v_a_3329_ = lean_ctor_get(v___y_3324_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___y_3324_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___y_3324_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___y_3324_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3350_, lean_object* v_params_3351_, lean_object* v_a_3352_, lean_object* v_snd_3353_, lean_object* v_alts_3354_, lean_object* v_as_3355_, lean_object* v_i_3356_, lean_object* v_j_3357_, lean_object* v_bs_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3350_, v_params_3351_, v_a_3352_, v_snd_3353_, v_alts_3354_, v_as_3355_, v_i_3356_, v_j_3357_, v_bs_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v_as_3355_);
lean_dec_ref(v_params_3351_);
return v_res_3364_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_unsigned_to_nat(16u);
v___x_3367_ = lean_mk_array(v___x_3366_, v___x_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3368_, lean_object* v___x_3369_, uint8_t v___x_3370_, uint8_t v___x_3371_, uint8_t v___x_3372_, lean_object* v_ism1_x27_3373_, lean_object* v_is_3374_, lean_object* v___x_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v___x_3378_, lean_object* v_params_3379_, lean_object* v___x_3380_, lean_object* v___x_3381_, lean_object* v_heq_3382_, lean_object* v_val_3383_, lean_object* v___x_3384_, lean_object* v_tail_3385_, lean_object* v_alts_3386_, lean_object* v___x_3387_, lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v_declName_3390_, lean_object* v_levelParams_3391_, lean_object* v_numIndices_3392_, lean_object* v___x_3393_, lean_object* v_numParams_3394_, lean_object* v_snd_3395_, lean_object* v_ism2_x27_3396_, lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3403_ = lean_box(v___x_3370_);
v___x_3404_ = lean_box(v___x_3371_);
v___x_3405_ = lean_box(v___x_3372_);
lean_inc_ref(v___x_3375_);
lean_inc_ref(v_is_3374_);
lean_inc_ref(v_ism1_x27_3373_);
lean_inc_ref(v_motive_3368_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3406_, 0, v_motive_3368_);
lean_closure_set(v___f_3406_, 1, v___x_3369_);
lean_closure_set(v___f_3406_, 2, v___x_3403_);
lean_closure_set(v___f_3406_, 3, v___x_3404_);
lean_closure_set(v___f_3406_, 4, v___x_3405_);
lean_closure_set(v___f_3406_, 5, v_ism1_x27_3373_);
lean_closure_set(v___f_3406_, 6, v_ism2_x27_3396_);
lean_closure_set(v___f_3406_, 7, v_is_3374_);
lean_closure_set(v___f_3406_, 8, v___x_3375_);
lean_inc_ref(v___x_3376_);
lean_inc_ref(v_is_3374_);
v___x_3407_ = lean_array_push(v_is_3374_, v___x_3376_);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
v___x_3408_ = l_Lean_Meta_withNewEqs___redArg(v___x_3407_, v_ism1_x27_3373_, v___f_3406_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3513_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v_fst_3410_ = lean_ctor_get(v_a_3409_, 0);
v_snd_3411_ = lean_ctor_get(v_a_3409_, 1);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_a_3409_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3413_ = v_a_3409_;
v_isShared_3414_ = v_isSharedCheck_3513_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3410_);
lean_dec(v_a_3409_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3513_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3415_ = l_Lean_mkConst(v___x_3377_, v___x_3378_);
v___x_3416_ = l_Lean_mkAppN(v___x_3415_, v_params_3379_);
v___x_3417_ = l_Lean_Expr_app___override(v___x_3416_, v_fst_3410_);
lean_inc_ref(v_is_3374_);
v___x_3418_ = l_Array_append___redArg(v_is_3374_, v___x_3380_);
v___x_3419_ = l_Array_append___redArg(v___x_3418_, v_is_3374_);
v___x_3420_ = l_Array_append___redArg(v___x_3419_, v___x_3381_);
v___x_3421_ = l_Lean_mkAppN(v___x_3417_, v___x_3420_);
lean_dec_ref(v___x_3420_);
lean_inc_ref(v_heq_3382_);
v___x_3422_ = l_Lean_Expr_app___override(v___x_3421_, v_heq_3382_);
v___x_3423_ = l_Lean_InductiveVal_numCtors(v_val_3383_);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc_ref(v___x_3422_);
v___x_3424_ = l_Lean_Meta_inferArgumentTypesN(v___x_3423_, v___x_3422_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = lean_mk_empty_array_with_capacity(v___x_3384_);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___x_3388_);
lean_inc_ref(v_alts_3386_);
lean_inc(v_snd_3411_);
v___x_3427_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3385_, v_params_3379_, v_a_3425_, v_snd_3411_, v_alts_3386_, v___x_3387_, v___x_3384_, v___x_3388_, v___x_3426_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = l_Lean_mkAppN(v___x_3422_, v_a_3428_);
lean_dec(v_a_3428_);
v___x_3430_ = l_Lean_mkAppN(v___x_3429_, v_snd_3411_);
lean_dec(v_snd_3411_);
lean_inc_ref(v___x_3389_);
v___x_3431_ = lean_array_push(v___x_3389_, v_motive_3368_);
v___x_3432_ = l_Array_append___redArg(v_params_3379_, v___x_3431_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = l_Array_append___redArg(v___x_3432_, v_is_3374_);
lean_dec_ref(v_is_3374_);
v___x_3434_ = lean_unsigned_to_nat(2u);
v___x_3435_ = lean_mk_empty_array_with_capacity(v___x_3434_);
v___x_3436_ = lean_array_push(v___x_3435_, v___x_3376_);
v___x_3437_ = lean_array_push(v___x_3436_, v___x_3375_);
v___x_3438_ = l_Array_append___redArg(v___x_3433_, v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = lean_array_push(v___x_3389_, v_heq_3382_);
v___x_3440_ = l_Array_append___redArg(v___x_3438_, v___x_3439_);
lean_dec_ref(v___x_3439_);
v___x_3441_ = l_Array_append___redArg(v___x_3440_, v_alts_3386_);
lean_dec_ref(v_alts_3386_);
v___x_3442_ = l_Lean_Meta_mkLambdaFVars(v___x_3441_, v___x_3430_, v___x_3370_, v___x_3371_, v___x_3370_, v___x_3371_, v___x_3372_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec_ref(v___x_3441_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref(v___x_3442_);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v_a_3443_);
v___x_3444_ = lean_infer_type(v_a_3443_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3480_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = lean_box(1);
lean_inc(v_declName_3390_);
v___x_3447_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3390_, v_levelParams_3391_, v_a_3445_, v_a_3443_, v___x_3446_, v___y_3401_);
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3480_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3480_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 1);
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; lean_object* v___f_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3454_ = lean_box(v___x_3370_);
lean_inc_ref(v___x_3453_);
v___f_3455_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3455_, 0, v___x_3453_);
lean_closure_set(v___f_3455_, 1, v___x_3454_);
v___x_3456_ = lean_nat_add(v_numIndices_3392_, v___x_3393_);
lean_inc(v___x_3388_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3388_);
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_mk_empty_array_with_capacity(v___x_3393_);
v___x_3460_ = lean_array_push(v___x_3459_, v___x_3458_);
v___x_3461_ = lean_array_push(v___x_3460_, v___x_3458_);
v___x_3462_ = lean_array_push(v___x_3461_, v___x_3458_);
v___x_3463_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v___x_3463_);
lean_ctor_set(v___x_3413_, 0, v___x_3388_);
v___x_3465_ = v___x_3413_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; uint8_t v___y_3468_; uint8_t v___x_3477_; 
v___x_3466_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3466_, 0, v_numParams_3394_);
lean_ctor_set(v___x_3466_, 1, v___x_3456_);
lean_ctor_set(v___x_3466_, 2, v_snd_3395_);
lean_ctor_set(v___x_3466_, 3, v___x_3457_);
lean_ctor_set(v___x_3466_, 4, v___x_3462_);
lean_ctor_set(v___x_3466_, 5, v___x_3465_);
v___x_3477_ = l_Lean_isPrivateName(v_declName_3390_);
if (v___x_3477_ == 0)
{
v___y_3468_ = v___x_3371_;
goto v___jp_3467_;
}
else
{
v___y_3468_ = v___x_3370_;
goto v___jp_3467_;
}
v___jp_3467_:
{
lean_object* v___x_3469_; 
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
v___x_3469_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3455_, v___y_3468_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec_ref(v___x_3469_);
v___x_3470_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3390_);
v___x_3471_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3470_, v_declName_3390_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v___x_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; 
lean_dec_ref(v___x_3471_);
lean_inc(v_declName_3390_);
v___x_3472_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3390_, v___x_3466_, v___y_3399_, v___y_3401_);
lean_dec_ref(v___x_3472_);
v___x_3473_ = 0;
lean_inc(v_declName_3390_);
v___x_3474_ = l_Lean_Meta_setInlineAttribute(v_declName_3390_, v___x_3473_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref(v___x_3474_);
lean_inc_ref(v___y_3400_);
v___x_3475_ = l_Lean_enableRealizationsForConst(v_declName_3390_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref(v___x_3475_);
v___x_3476_ = l_Lean_compileDecl(v___x_3453_, v___x_3371_, v___y_3400_, v___y_3401_);
return v___x_3476_;
}
else
{
lean_dec_ref(v___x_3453_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
return v___x_3475_;
}
}
else
{
lean_dec_ref(v___x_3453_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v_declName_3390_);
return v___x_3474_;
}
}
else
{
lean_dec_ref(v___x_3466_);
lean_dec_ref(v___x_3453_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v_declName_3390_);
return v___x_3471_;
}
}
else
{
lean_dec_ref(v___x_3466_);
lean_dec_ref(v___x_3453_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v_declName_3390_);
return v___x_3469_;
}
}
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_a_3443_);
lean_del_object(v___x_3413_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_snd_3395_);
lean_dec(v_numParams_3394_);
lean_dec(v_levelParams_3391_);
lean_dec(v_declName_3390_);
lean_dec(v___x_3388_);
v_a_3481_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3444_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3444_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_del_object(v___x_3413_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_snd_3395_);
lean_dec(v_numParams_3394_);
lean_dec(v_levelParams_3391_);
lean_dec(v_declName_3390_);
lean_dec(v___x_3388_);
v_a_3489_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3442_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3442_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_snd_3395_);
lean_dec(v_numParams_3394_);
lean_dec(v_levelParams_3391_);
lean_dec(v_declName_3390_);
lean_dec_ref(v___x_3389_);
lean_dec(v___x_3388_);
lean_dec_ref(v_alts_3386_);
lean_dec_ref(v_heq_3382_);
lean_dec_ref(v_params_3379_);
lean_dec_ref(v___x_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_is_3374_);
lean_dec_ref(v_motive_3368_);
v_a_3497_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3427_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3427_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v___x_3422_);
lean_del_object(v___x_3413_);
lean_dec(v_snd_3411_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_snd_3395_);
lean_dec(v_numParams_3394_);
lean_dec(v_levelParams_3391_);
lean_dec(v_declName_3390_);
lean_dec_ref(v___x_3389_);
lean_dec(v___x_3388_);
lean_dec_ref(v_alts_3386_);
lean_dec(v_tail_3385_);
lean_dec(v___x_3384_);
lean_dec_ref(v_heq_3382_);
lean_dec_ref(v_params_3379_);
lean_dec_ref(v___x_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_is_3374_);
lean_dec_ref(v_motive_3368_);
v_a_3505_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3424_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3424_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_snd_3395_);
lean_dec(v_numParams_3394_);
lean_dec(v_levelParams_3391_);
lean_dec(v_declName_3390_);
lean_dec_ref(v___x_3389_);
lean_dec(v___x_3388_);
lean_dec_ref(v_alts_3386_);
lean_dec(v_tail_3385_);
lean_dec(v___x_3384_);
lean_dec_ref(v_heq_3382_);
lean_dec_ref(v_params_3379_);
lean_dec(v___x_3378_);
lean_dec(v___x_3377_);
lean_dec_ref(v___x_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_is_3374_);
lean_dec_ref(v_motive_3368_);
v_a_3514_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3408_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3408_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3522_ = _args[0];
lean_object* v___x_3523_ = _args[1];
lean_object* v___x_3524_ = _args[2];
lean_object* v___x_3525_ = _args[3];
lean_object* v___x_3526_ = _args[4];
lean_object* v_ism1_x27_3527_ = _args[5];
lean_object* v_is_3528_ = _args[6];
lean_object* v___x_3529_ = _args[7];
lean_object* v___x_3530_ = _args[8];
lean_object* v___x_3531_ = _args[9];
lean_object* v___x_3532_ = _args[10];
lean_object* v_params_3533_ = _args[11];
lean_object* v___x_3534_ = _args[12];
lean_object* v___x_3535_ = _args[13];
lean_object* v_heq_3536_ = _args[14];
lean_object* v_val_3537_ = _args[15];
lean_object* v___x_3538_ = _args[16];
lean_object* v_tail_3539_ = _args[17];
lean_object* v_alts_3540_ = _args[18];
lean_object* v___x_3541_ = _args[19];
lean_object* v___x_3542_ = _args[20];
lean_object* v___x_3543_ = _args[21];
lean_object* v_declName_3544_ = _args[22];
lean_object* v_levelParams_3545_ = _args[23];
lean_object* v_numIndices_3546_ = _args[24];
lean_object* v___x_3547_ = _args[25];
lean_object* v_numParams_3548_ = _args[26];
lean_object* v_snd_3549_ = _args[27];
lean_object* v_ism2_x27_3550_ = _args[28];
lean_object* v_x_3551_ = _args[29];
lean_object* v___y_3552_ = _args[30];
lean_object* v___y_3553_ = _args[31];
lean_object* v___y_3554_ = _args[32];
lean_object* v___y_3555_ = _args[33];
lean_object* v___y_3556_ = _args[34];
_start:
{
uint8_t v___x_15707__boxed_3557_; uint8_t v___x_15708__boxed_3558_; uint8_t v___x_15709__boxed_3559_; lean_object* v_res_3560_; 
v___x_15707__boxed_3557_ = lean_unbox(v___x_3524_);
v___x_15708__boxed_3558_ = lean_unbox(v___x_3525_);
v___x_15709__boxed_3559_ = lean_unbox(v___x_3526_);
v_res_3560_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3522_, v___x_3523_, v___x_15707__boxed_3557_, v___x_15708__boxed_3558_, v___x_15709__boxed_3559_, v_ism1_x27_3527_, v_is_3528_, v___x_3529_, v___x_3530_, v___x_3531_, v___x_3532_, v_params_3533_, v___x_3534_, v___x_3535_, v_heq_3536_, v_val_3537_, v___x_3538_, v_tail_3539_, v_alts_3540_, v___x_3541_, v___x_3542_, v___x_3543_, v_declName_3544_, v_levelParams_3545_, v_numIndices_3546_, v___x_3547_, v_numParams_3548_, v_snd_3549_, v_ism2_x27_3550_, v_x_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec_ref(v_x_3551_);
lean_dec(v___x_3547_);
lean_dec(v_numIndices_3546_);
lean_dec_ref(v___x_3541_);
lean_dec_ref(v_val_3537_);
lean_dec_ref(v___x_3535_);
lean_dec_ref(v___x_3534_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3561_, lean_object* v___x_3562_, uint8_t v___x_3563_, uint8_t v___x_3564_, uint8_t v___x_3565_, lean_object* v_is_3566_, lean_object* v___x_3567_, lean_object* v___x_3568_, lean_object* v___x_3569_, lean_object* v___x_3570_, lean_object* v_params_3571_, lean_object* v___x_3572_, lean_object* v___x_3573_, lean_object* v_heq_3574_, lean_object* v_val_3575_, lean_object* v___x_3576_, lean_object* v_tail_3577_, lean_object* v_alts_3578_, lean_object* v___x_3579_, lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v_declName_3582_, lean_object* v_levelParams_3583_, lean_object* v_numIndices_3584_, lean_object* v___x_3585_, lean_object* v_numParams_3586_, lean_object* v_snd_3587_, lean_object* v___x_3588_, lean_object* v___x_3589_, lean_object* v_ism1_x27_3590_, lean_object* v_x_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___f_3600_; lean_object* v___x_3601_; 
v___x_3597_ = lean_box(v___x_3563_);
v___x_3598_ = lean_box(v___x_3564_);
v___x_3599_ = lean_box(v___x_3565_);
v___f_3600_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 35, 28);
lean_closure_set(v___f_3600_, 0, v_motive_3561_);
lean_closure_set(v___f_3600_, 1, v___x_3562_);
lean_closure_set(v___f_3600_, 2, v___x_3597_);
lean_closure_set(v___f_3600_, 3, v___x_3598_);
lean_closure_set(v___f_3600_, 4, v___x_3599_);
lean_closure_set(v___f_3600_, 5, v_ism1_x27_3590_);
lean_closure_set(v___f_3600_, 6, v_is_3566_);
lean_closure_set(v___f_3600_, 7, v___x_3567_);
lean_closure_set(v___f_3600_, 8, v___x_3568_);
lean_closure_set(v___f_3600_, 9, v___x_3569_);
lean_closure_set(v___f_3600_, 10, v___x_3570_);
lean_closure_set(v___f_3600_, 11, v_params_3571_);
lean_closure_set(v___f_3600_, 12, v___x_3572_);
lean_closure_set(v___f_3600_, 13, v___x_3573_);
lean_closure_set(v___f_3600_, 14, v_heq_3574_);
lean_closure_set(v___f_3600_, 15, v_val_3575_);
lean_closure_set(v___f_3600_, 16, v___x_3576_);
lean_closure_set(v___f_3600_, 17, v_tail_3577_);
lean_closure_set(v___f_3600_, 18, v_alts_3578_);
lean_closure_set(v___f_3600_, 19, v___x_3579_);
lean_closure_set(v___f_3600_, 20, v___x_3580_);
lean_closure_set(v___f_3600_, 21, v___x_3581_);
lean_closure_set(v___f_3600_, 22, v_declName_3582_);
lean_closure_set(v___f_3600_, 23, v_levelParams_3583_);
lean_closure_set(v___f_3600_, 24, v_numIndices_3584_);
lean_closure_set(v___f_3600_, 25, v___x_3585_);
lean_closure_set(v___f_3600_, 26, v_numParams_3586_);
lean_closure_set(v___f_3600_, 27, v_snd_3587_);
v___x_3601_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3588_, v___x_3589_, v___f_3600_, v___x_3563_, v___x_3563_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3602_ = _args[0];
lean_object* v___x_3603_ = _args[1];
lean_object* v___x_3604_ = _args[2];
lean_object* v___x_3605_ = _args[3];
lean_object* v___x_3606_ = _args[4];
lean_object* v_is_3607_ = _args[5];
lean_object* v___x_3608_ = _args[6];
lean_object* v___x_3609_ = _args[7];
lean_object* v___x_3610_ = _args[8];
lean_object* v___x_3611_ = _args[9];
lean_object* v_params_3612_ = _args[10];
lean_object* v___x_3613_ = _args[11];
lean_object* v___x_3614_ = _args[12];
lean_object* v_heq_3615_ = _args[13];
lean_object* v_val_3616_ = _args[14];
lean_object* v___x_3617_ = _args[15];
lean_object* v_tail_3618_ = _args[16];
lean_object* v_alts_3619_ = _args[17];
lean_object* v___x_3620_ = _args[18];
lean_object* v___x_3621_ = _args[19];
lean_object* v___x_3622_ = _args[20];
lean_object* v_declName_3623_ = _args[21];
lean_object* v_levelParams_3624_ = _args[22];
lean_object* v_numIndices_3625_ = _args[23];
lean_object* v___x_3626_ = _args[24];
lean_object* v_numParams_3627_ = _args[25];
lean_object* v_snd_3628_ = _args[26];
lean_object* v___x_3629_ = _args[27];
lean_object* v___x_3630_ = _args[28];
lean_object* v_ism1_x27_3631_ = _args[29];
lean_object* v_x_3632_ = _args[30];
lean_object* v___y_3633_ = _args[31];
lean_object* v___y_3634_ = _args[32];
lean_object* v___y_3635_ = _args[33];
lean_object* v___y_3636_ = _args[34];
lean_object* v___y_3637_ = _args[35];
_start:
{
uint8_t v___x_16031__boxed_3638_; uint8_t v___x_16032__boxed_3639_; uint8_t v___x_16033__boxed_3640_; lean_object* v_res_3641_; 
v___x_16031__boxed_3638_ = lean_unbox(v___x_3604_);
v___x_16032__boxed_3639_ = lean_unbox(v___x_3605_);
v___x_16033__boxed_3640_ = lean_unbox(v___x_3606_);
v_res_3641_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3602_, v___x_3603_, v___x_16031__boxed_3638_, v___x_16032__boxed_3639_, v___x_16033__boxed_3640_, v_is_3607_, v___x_3608_, v___x_3609_, v___x_3610_, v___x_3611_, v_params_3612_, v___x_3613_, v___x_3614_, v_heq_3615_, v_val_3616_, v___x_3617_, v_tail_3618_, v_alts_3619_, v___x_3620_, v___x_3621_, v___x_3622_, v_declName_3623_, v_levelParams_3624_, v_numIndices_3625_, v___x_3626_, v_numParams_3627_, v_snd_3628_, v___x_3629_, v___x_3630_, v_ism1_x27_3631_, v_x_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec_ref(v_x_3632_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3642_, lean_object* v___x_3643_, lean_object* v_motive_3644_, lean_object* v___x_3645_, uint8_t v___x_3646_, uint8_t v___x_3647_, uint8_t v___x_3648_, lean_object* v_is_3649_, lean_object* v___x_3650_, lean_object* v___x_3651_, lean_object* v___x_3652_, lean_object* v___x_3653_, lean_object* v_params_3654_, lean_object* v___x_3655_, lean_object* v___x_3656_, lean_object* v_heq_3657_, lean_object* v_val_3658_, lean_object* v___x_3659_, lean_object* v_tail_3660_, lean_object* v___x_3661_, lean_object* v___x_3662_, lean_object* v___x_3663_, lean_object* v_declName_3664_, lean_object* v_levelParams_3665_, lean_object* v___x_3666_, lean_object* v_numParams_3667_, lean_object* v_snd_3668_, lean_object* v___x_3669_, lean_object* v_alts_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___f_3681_; lean_object* v___x_3682_; 
v___x_3676_ = lean_nat_add(v_numIndices_3642_, v___x_3643_);
v___x_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
v___x_3678_ = lean_box(v___x_3646_);
v___x_3679_ = lean_box(v___x_3647_);
v___x_3680_ = lean_box(v___x_3648_);
lean_inc_ref(v___x_3677_);
lean_inc_ref(v___x_3669_);
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 36, 29);
lean_closure_set(v___f_3681_, 0, v_motive_3644_);
lean_closure_set(v___f_3681_, 1, v___x_3645_);
lean_closure_set(v___f_3681_, 2, v___x_3678_);
lean_closure_set(v___f_3681_, 3, v___x_3679_);
lean_closure_set(v___f_3681_, 4, v___x_3680_);
lean_closure_set(v___f_3681_, 5, v_is_3649_);
lean_closure_set(v___f_3681_, 6, v___x_3650_);
lean_closure_set(v___f_3681_, 7, v___x_3651_);
lean_closure_set(v___f_3681_, 8, v___x_3652_);
lean_closure_set(v___f_3681_, 9, v___x_3653_);
lean_closure_set(v___f_3681_, 10, v_params_3654_);
lean_closure_set(v___f_3681_, 11, v___x_3655_);
lean_closure_set(v___f_3681_, 12, v___x_3656_);
lean_closure_set(v___f_3681_, 13, v_heq_3657_);
lean_closure_set(v___f_3681_, 14, v_val_3658_);
lean_closure_set(v___f_3681_, 15, v___x_3659_);
lean_closure_set(v___f_3681_, 16, v_tail_3660_);
lean_closure_set(v___f_3681_, 17, v_alts_3670_);
lean_closure_set(v___f_3681_, 18, v___x_3661_);
lean_closure_set(v___f_3681_, 19, v___x_3662_);
lean_closure_set(v___f_3681_, 20, v___x_3663_);
lean_closure_set(v___f_3681_, 21, v_declName_3664_);
lean_closure_set(v___f_3681_, 22, v_levelParams_3665_);
lean_closure_set(v___f_3681_, 23, v_numIndices_3642_);
lean_closure_set(v___f_3681_, 24, v___x_3666_);
lean_closure_set(v___f_3681_, 25, v_numParams_3667_);
lean_closure_set(v___f_3681_, 26, v_snd_3668_);
lean_closure_set(v___f_3681_, 27, v___x_3669_);
lean_closure_set(v___f_3681_, 28, v___x_3677_);
v___x_3682_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3669_, v___x_3677_, v___f_3681_, v___x_3646_, v___x_3646_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3683_ = _args[0];
lean_object* v___x_3684_ = _args[1];
lean_object* v_motive_3685_ = _args[2];
lean_object* v___x_3686_ = _args[3];
lean_object* v___x_3687_ = _args[4];
lean_object* v___x_3688_ = _args[5];
lean_object* v___x_3689_ = _args[6];
lean_object* v_is_3690_ = _args[7];
lean_object* v___x_3691_ = _args[8];
lean_object* v___x_3692_ = _args[9];
lean_object* v___x_3693_ = _args[10];
lean_object* v___x_3694_ = _args[11];
lean_object* v_params_3695_ = _args[12];
lean_object* v___x_3696_ = _args[13];
lean_object* v___x_3697_ = _args[14];
lean_object* v_heq_3698_ = _args[15];
lean_object* v_val_3699_ = _args[16];
lean_object* v___x_3700_ = _args[17];
lean_object* v_tail_3701_ = _args[18];
lean_object* v___x_3702_ = _args[19];
lean_object* v___x_3703_ = _args[20];
lean_object* v___x_3704_ = _args[21];
lean_object* v_declName_3705_ = _args[22];
lean_object* v_levelParams_3706_ = _args[23];
lean_object* v___x_3707_ = _args[24];
lean_object* v_numParams_3708_ = _args[25];
lean_object* v_snd_3709_ = _args[26];
lean_object* v___x_3710_ = _args[27];
lean_object* v_alts_3711_ = _args[28];
lean_object* v___y_3712_ = _args[29];
lean_object* v___y_3713_ = _args[30];
lean_object* v___y_3714_ = _args[31];
lean_object* v___y_3715_ = _args[32];
lean_object* v___y_3716_ = _args[33];
_start:
{
uint8_t v___x_16120__boxed_3717_; uint8_t v___x_16121__boxed_3718_; uint8_t v___x_16122__boxed_3719_; lean_object* v_res_3720_; 
v___x_16120__boxed_3717_ = lean_unbox(v___x_3687_);
v___x_16121__boxed_3718_ = lean_unbox(v___x_3688_);
v___x_16122__boxed_3719_ = lean_unbox(v___x_3689_);
v_res_3720_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3683_, v___x_3684_, v_motive_3685_, v___x_3686_, v___x_16120__boxed_3717_, v___x_16121__boxed_3718_, v___x_16122__boxed_3719_, v_is_3690_, v___x_3691_, v___x_3692_, v___x_3693_, v___x_3694_, v_params_3695_, v___x_3696_, v___x_3697_, v_heq_3698_, v_val_3699_, v___x_3700_, v_tail_3701_, v___x_3702_, v___x_3703_, v___x_3704_, v_declName_3705_, v_levelParams_3706_, v___x_3707_, v_numParams_3708_, v_snd_3709_, v___x_3710_, v_alts_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___x_3684_);
return v_res_3720_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = lean_box(0);
v___x_3724_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3725_ = l_Lean_mkConst(v___x_3724_, v___x_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v_j_3726_, lean_object* v___x_3727_, lean_object* v_motive_3728_, uint8_t v_isZero_3729_, uint8_t v___x_3730_, uint8_t v___x_3731_, lean_object* v___x_3732_, lean_object* v___x_3733_, lean_object* v___x_3734_, lean_object* v_zs12_3735_, lean_object* v_is_3736_, lean_object* v_fields1_3737_, lean_object* v_fields2_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v_e_3754_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_inc(v_j_3726_);
v___x_3764_ = l_Lean_mkNatLit(v_j_3726_);
lean_inc(v___y_3742_);
lean_inc_ref(v___y_3741_);
lean_inc(v___y_3740_);
lean_inc_ref(v___y_3739_);
v___x_3765_ = l_Lean_Meta_mkEqRefl(v___x_3764_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
lean_inc_ref(v___x_3727_);
v___x_3767_ = l_Lean_mkAppN(v___x_3727_, v_fields1_3737_);
v___x_3768_ = l_Lean_mkAppN(v___x_3727_, v_fields2_3738_);
v___x_3769_ = lean_unsigned_to_nat(3u);
v___x_3770_ = lean_mk_empty_array_with_capacity(v___x_3769_);
v___x_3771_ = lean_array_push(v___x_3770_, v___x_3767_);
v___x_3772_ = lean_array_push(v___x_3771_, v___x_3768_);
v___x_3773_ = lean_array_push(v___x_3772_, v_a_3766_);
v___x_3774_ = l_Array_append___redArg(v_is_3736_, v___x_3773_);
lean_dec_ref(v___x_3773_);
v___x_3775_ = l_Lean_mkAppN(v_motive_3728_, v___x_3774_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = l_Lean_Meta_mkForallFVars(v_zs12_3735_, v___x_3775_, v_isZero_3729_, v___x_3730_, v___x_3730_, v___x_3731_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = lean_array_get_size(v_zs12_3735_);
v___x_3779_ = lean_nat_dec_eq(v___x_3778_, v___x_3732_);
if (v___x_3779_ == 0)
{
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
v_e_3754_ = v_a_3777_;
goto v___jp_3753_;
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3781_ = l_Lean_mkArrow(v___x_3780_, v_a_3777_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
v_e_3754_ = v_a_3782_;
goto v___jp_3753_;
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec(v___x_3733_);
lean_dec(v___x_3732_);
lean_dec(v_j_3726_);
v_a_3783_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3781_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3781_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___x_3733_);
lean_dec(v___x_3732_);
lean_dec(v_j_3726_);
v_a_3791_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3776_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3776_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec_ref(v_is_3736_);
lean_dec(v___x_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_motive_3728_);
lean_dec_ref(v___x_3727_);
lean_dec(v_j_3726_);
v_a_3799_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3765_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3765_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
v___jp_3744_:
{
lean_object* v___x_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3747_ = lean_array_get_size(v_zs12_3735_);
v___x_3748_ = lean_nat_dec_eq(v___x_3747_, v___x_3732_);
v___x_3749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3732_);
lean_ctor_set_uint8(v___x_3749_, sizeof(void*)*2, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___y_3746_);
lean_ctor_set(v___x_3750_, 1, v___y_3745_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v___x_3749_);
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
return v___x_3752_;
}
v___jp_3753_:
{
if (lean_obj_tag(v___x_3733_) == 1)
{
lean_object* v_str_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec(v_j_3726_);
v_str_3755_ = lean_ctor_get(v___x_3733_, 1);
lean_inc_ref(v_str_3755_);
lean_dec_ref(v___x_3733_);
v___x_3756_ = lean_box(0);
v___x_3757_ = l_Lean_Name_str___override(v___x_3756_, v_str_3755_);
v___y_3745_ = v_e_3754_;
v___y_3746_ = v___x_3757_;
goto v___jp_3744_;
}
else
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec(v___x_3733_);
v___x_3758_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3759_ = lean_nat_add(v_j_3726_, v___x_3734_);
lean_dec(v_j_3726_);
v___x_3760_ = l_Nat_reprFast(v___x_3759_);
v___x_3761_ = lean_string_append(v___x_3758_, v___x_3760_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = lean_box(0);
v___x_3763_ = l_Lean_Name_str___override(v___x_3762_, v___x_3761_);
v___y_3745_ = v_e_3754_;
v___y_3746_ = v___x_3763_;
goto v___jp_3744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_j_3807_ = _args[0];
lean_object* v___x_3808_ = _args[1];
lean_object* v_motive_3809_ = _args[2];
lean_object* v_isZero_3810_ = _args[3];
lean_object* v___x_3811_ = _args[4];
lean_object* v___x_3812_ = _args[5];
lean_object* v___x_3813_ = _args[6];
lean_object* v___x_3814_ = _args[7];
lean_object* v___x_3815_ = _args[8];
lean_object* v_zs12_3816_ = _args[9];
lean_object* v_is_3817_ = _args[10];
lean_object* v_fields1_3818_ = _args[11];
lean_object* v_fields2_3819_ = _args[12];
lean_object* v___y_3820_ = _args[13];
lean_object* v___y_3821_ = _args[14];
lean_object* v___y_3822_ = _args[15];
lean_object* v___y_3823_ = _args[16];
lean_object* v___y_3824_ = _args[17];
_start:
{
uint8_t v_isZero_boxed_3825_; uint8_t v___x_16220__boxed_3826_; uint8_t v___x_16221__boxed_3827_; lean_object* v_res_3828_; 
v_isZero_boxed_3825_ = lean_unbox(v_isZero_3810_);
v___x_16220__boxed_3826_ = lean_unbox(v___x_3811_);
v___x_16221__boxed_3827_ = lean_unbox(v___x_3812_);
v_res_3828_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v_j_3807_, v___x_3808_, v_motive_3809_, v_isZero_boxed_3825_, v___x_16220__boxed_3826_, v___x_16221__boxed_3827_, v___x_3813_, v___x_3814_, v___x_3815_, v_zs12_3816_, v_is_3817_, v_fields1_3818_, v_fields2_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec_ref(v_fields2_3819_);
lean_dec_ref(v_fields1_3818_);
lean_dec_ref(v_zs12_3816_);
lean_dec(v___x_3815_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3829_, lean_object* v_params_3830_, lean_object* v_motive_3831_, lean_object* v_as_3832_, lean_object* v_i_3833_, lean_object* v_j_3834_, lean_object* v_bs_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_zero_3841_; uint8_t v_isZero_3842_; 
v_zero_3841_ = lean_unsigned_to_nat(0u);
v_isZero_3842_ = lean_nat_dec_eq(v_i_3833_, v_zero_3841_);
if (v_isZero_3842_ == 1)
{
lean_object* v___x_3843_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v_j_3834_);
lean_dec(v_i_3833_);
lean_dec_ref(v_motive_3831_);
lean_dec(v_tail_3829_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_bs_3835_);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; uint8_t v___x_3845_; uint8_t v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___f_3853_; lean_object* v___x_3854_; 
v___x_3844_ = lean_unsigned_to_nat(1u);
v___x_3845_ = 1;
v___x_3846_ = 1;
v___x_3847_ = lean_array_fget_borrowed(v_as_3832_, v_j_3834_);
lean_inc(v_tail_3829_);
lean_inc(v___x_3847_);
v___x_3848_ = l_Lean_mkConst(v___x_3847_, v_tail_3829_);
v___x_3849_ = l_Lean_mkAppN(v___x_3848_, v_params_3830_);
v___x_3850_ = lean_box(v_isZero_3842_);
v___x_3851_ = lean_box(v___x_3845_);
v___x_3852_ = lean_box(v___x_3846_);
lean_inc(v___x_3847_);
lean_inc_ref(v_motive_3831_);
lean_inc_ref(v___x_3849_);
lean_inc(v_j_3834_);
v___f_3853_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3853_, 0, v_j_3834_);
lean_closure_set(v___f_3853_, 1, v___x_3849_);
lean_closure_set(v___f_3853_, 2, v_motive_3831_);
lean_closure_set(v___f_3853_, 3, v___x_3850_);
lean_closure_set(v___f_3853_, 4, v___x_3851_);
lean_closure_set(v___f_3853_, 5, v___x_3852_);
lean_closure_set(v___f_3853_, 6, v_zero_3841_);
lean_closure_set(v___f_3853_, 7, v___x_3847_);
lean_closure_set(v___f_3853_, 8, v___x_3844_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v___y_3836_);
v___x_3854_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3849_, v___f_3853_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v_n_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
v_n_3856_ = lean_nat_sub(v_i_3833_, v___x_3844_);
lean_dec(v_i_3833_);
v___x_3857_ = lean_nat_add(v_j_3834_, v___x_3844_);
lean_dec(v_j_3834_);
v___x_3858_ = lean_array_push(v_bs_3835_, v_a_3855_);
v_i_3833_ = v_n_3856_;
v_j_3834_ = v___x_3857_;
v_bs_3835_ = v___x_3858_;
goto _start;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v_bs_3835_);
lean_dec(v_j_3834_);
lean_dec(v_i_3833_);
lean_dec_ref(v_motive_3831_);
lean_dec(v_tail_3829_);
v_a_3860_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3854_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3854_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3868_, lean_object* v_params_3869_, lean_object* v_motive_3870_, lean_object* v_as_3871_, lean_object* v_i_3872_, lean_object* v_j_3873_, lean_object* v_bs_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3868_, v_params_3869_, v_motive_3870_, v_as_3871_, v_i_3872_, v_j_3873_, v_bs_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec_ref(v_as_3871_);
lean_dec_ref(v_params_3869_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3881_, lean_object* v_tail_3882_, lean_object* v_params_3883_, lean_object* v___x_3884_, lean_object* v_numIndices_3885_, lean_object* v___x_3886_, lean_object* v___x_3887_, uint8_t v___x_3888_, uint8_t v___x_3889_, uint8_t v___x_3890_, lean_object* v_is_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v___x_3897_, lean_object* v_heq_3898_, lean_object* v_val_3899_, lean_object* v___x_3900_, lean_object* v_declName_3901_, lean_object* v_levelParams_3902_, lean_object* v___x_3903_, lean_object* v_numParams_3904_, lean_object* v___x_3905_, lean_object* v___x_3906_, lean_object* v_motive_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3913_ = lean_array_mk(v_ctors_3881_);
v___x_3914_ = lean_array_get_size(v___x_3913_);
v___x_3915_ = lean_mk_empty_array_with_capacity(v___x_3914_);
lean_inc(v___y_3911_);
lean_inc_ref(v___y_3910_);
lean_inc(v___y_3909_);
lean_inc_ref(v___y_3908_);
lean_inc(v___x_3884_);
lean_inc_ref(v_motive_3907_);
lean_inc(v_tail_3882_);
v___x_3916_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3882_, v_params_3883_, v_motive_3907_, v___x_3913_, v___x_3914_, v___x_3884_, v___x_3915_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v_fst_3919_; lean_object* v_snd_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___f_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
v___x_3918_ = l_Array_unzip___redArg(v_a_3917_);
lean_dec(v_a_3917_);
v_fst_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_fst_3919_);
v_snd_3920_ = lean_ctor_get(v___x_3918_, 1);
lean_inc(v_snd_3920_);
lean_dec_ref(v___x_3918_);
v___x_3921_ = lean_box(v___x_3888_);
v___x_3922_ = lean_box(v___x_3889_);
v___x_3923_ = lean_box(v___x_3890_);
v___f_3924_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 34, 28);
lean_closure_set(v___f_3924_, 0, v_numIndices_3885_);
lean_closure_set(v___f_3924_, 1, v___x_3886_);
lean_closure_set(v___f_3924_, 2, v_motive_3907_);
lean_closure_set(v___f_3924_, 3, v___x_3887_);
lean_closure_set(v___f_3924_, 4, v___x_3921_);
lean_closure_set(v___f_3924_, 5, v___x_3922_);
lean_closure_set(v___f_3924_, 6, v___x_3923_);
lean_closure_set(v___f_3924_, 7, v_is_3891_);
lean_closure_set(v___f_3924_, 8, v___x_3892_);
lean_closure_set(v___f_3924_, 9, v___x_3893_);
lean_closure_set(v___f_3924_, 10, v___x_3894_);
lean_closure_set(v___f_3924_, 11, v___x_3895_);
lean_closure_set(v___f_3924_, 12, v_params_3883_);
lean_closure_set(v___f_3924_, 13, v___x_3896_);
lean_closure_set(v___f_3924_, 14, v___x_3897_);
lean_closure_set(v___f_3924_, 15, v_heq_3898_);
lean_closure_set(v___f_3924_, 16, v_val_3899_);
lean_closure_set(v___f_3924_, 17, v___x_3914_);
lean_closure_set(v___f_3924_, 18, v_tail_3882_);
lean_closure_set(v___f_3924_, 19, v___x_3913_);
lean_closure_set(v___f_3924_, 20, v___x_3884_);
lean_closure_set(v___f_3924_, 21, v___x_3900_);
lean_closure_set(v___f_3924_, 22, v_declName_3901_);
lean_closure_set(v___f_3924_, 23, v_levelParams_3902_);
lean_closure_set(v___f_3924_, 24, v___x_3903_);
lean_closure_set(v___f_3924_, 25, v_numParams_3904_);
lean_closure_set(v___f_3924_, 26, v_snd_3920_);
lean_closure_set(v___f_3924_, 27, v___x_3905_);
v___x_3925_ = 0;
v___x_3926_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v___x_3906_, v_fst_3919_, v___f_3924_, v___x_3925_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
return v___x_3926_;
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v___x_3913_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec_ref(v_motive_3907_);
lean_dec_ref(v___x_3905_);
lean_dec(v_numParams_3904_);
lean_dec(v___x_3903_);
lean_dec(v_levelParams_3902_);
lean_dec(v_declName_3901_);
lean_dec_ref(v___x_3900_);
lean_dec_ref(v_val_3899_);
lean_dec_ref(v_heq_3898_);
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec(v___x_3895_);
lean_dec(v___x_3894_);
lean_dec_ref(v___x_3893_);
lean_dec_ref(v___x_3892_);
lean_dec_ref(v_is_3891_);
lean_dec_ref(v___x_3887_);
lean_dec(v___x_3886_);
lean_dec(v_numIndices_3885_);
lean_dec(v___x_3884_);
lean_dec_ref(v_params_3883_);
lean_dec(v_tail_3882_);
v_a_3927_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3916_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3916_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_3935_ = _args[0];
lean_object* v_tail_3936_ = _args[1];
lean_object* v_params_3937_ = _args[2];
lean_object* v___x_3938_ = _args[3];
lean_object* v_numIndices_3939_ = _args[4];
lean_object* v___x_3940_ = _args[5];
lean_object* v___x_3941_ = _args[6];
lean_object* v___x_3942_ = _args[7];
lean_object* v___x_3943_ = _args[8];
lean_object* v___x_3944_ = _args[9];
lean_object* v_is_3945_ = _args[10];
lean_object* v___x_3946_ = _args[11];
lean_object* v___x_3947_ = _args[12];
lean_object* v___x_3948_ = _args[13];
lean_object* v___x_3949_ = _args[14];
lean_object* v___x_3950_ = _args[15];
lean_object* v___x_3951_ = _args[16];
lean_object* v_heq_3952_ = _args[17];
lean_object* v_val_3953_ = _args[18];
lean_object* v___x_3954_ = _args[19];
lean_object* v_declName_3955_ = _args[20];
lean_object* v_levelParams_3956_ = _args[21];
lean_object* v___x_3957_ = _args[22];
lean_object* v_numParams_3958_ = _args[23];
lean_object* v___x_3959_ = _args[24];
lean_object* v___x_3960_ = _args[25];
lean_object* v_motive_3961_ = _args[26];
lean_object* v___y_3962_ = _args[27];
lean_object* v___y_3963_ = _args[28];
lean_object* v___y_3964_ = _args[29];
lean_object* v___y_3965_ = _args[30];
lean_object* v___y_3966_ = _args[31];
_start:
{
uint8_t v___x_16454__boxed_3967_; uint8_t v___x_16455__boxed_3968_; uint8_t v___x_16456__boxed_3969_; lean_object* v_res_3970_; 
v___x_16454__boxed_3967_ = lean_unbox(v___x_3942_);
v___x_16455__boxed_3968_ = lean_unbox(v___x_3943_);
v___x_16456__boxed_3969_ = lean_unbox(v___x_3944_);
v_res_3970_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_3935_, v_tail_3936_, v_params_3937_, v___x_3938_, v_numIndices_3939_, v___x_3940_, v___x_3941_, v___x_16454__boxed_3967_, v___x_16455__boxed_3968_, v___x_16456__boxed_3969_, v_is_3945_, v___x_3946_, v___x_3947_, v___x_3948_, v___x_3949_, v___x_3950_, v___x_3951_, v_heq_3952_, v_val_3953_, v___x_3954_, v_declName_3955_, v_levelParams_3956_, v___x_3957_, v_numParams_3958_, v___x_3959_, v___x_3960_, v_motive_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_3971_, lean_object* v___x_3972_, lean_object* v_is_3973_, lean_object* v_head_3974_, lean_object* v_ctors_3975_, lean_object* v_tail_3976_, lean_object* v_params_3977_, lean_object* v___x_3978_, lean_object* v_numIndices_3979_, lean_object* v___x_3980_, lean_object* v___x_3981_, lean_object* v___x_3982_, lean_object* v___x_3983_, lean_object* v___x_3984_, lean_object* v_val_3985_, lean_object* v___x_3986_, lean_object* v_declName_3987_, lean_object* v_levelParams_3988_, lean_object* v_numParams_3989_, lean_object* v___x_3990_, lean_object* v___x_3991_, lean_object* v_heq_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; uint8_t v___x_4006_; uint8_t v___x_4007_; lean_object* v___x_4008_; 
v___x_3998_ = lean_unsigned_to_nat(3u);
v___x_3999_ = lean_mk_empty_array_with_capacity(v___x_3998_);
lean_inc_ref(v___x_3971_);
v___x_4000_ = lean_array_push(v___x_3999_, v___x_3971_);
lean_inc_ref(v___x_3972_);
v___x_4001_ = lean_array_push(v___x_4000_, v___x_3972_);
lean_inc_ref(v_heq_3992_);
v___x_4002_ = lean_array_push(v___x_4001_, v_heq_3992_);
lean_inc_ref(v_is_3973_);
v___x_4003_ = l_Array_append___redArg(v_is_3973_, v___x_4002_);
lean_dec_ref(v___x_4002_);
v___x_4004_ = l_Lean_mkSort(v_head_3974_);
v___x_4005_ = 0;
v___x_4006_ = 1;
v___x_4007_ = 1;
v___x_4008_ = l_Lean_Meta_mkForallFVars(v___x_4003_, v___x_4004_, v___x_4005_, v___x_4006_, v___x_4006_, v___x_4007_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___f_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref(v___x_4008_);
v___x_4010_ = lean_box(v___x_4005_);
v___x_4011_ = lean_box(v___x_4006_);
v___x_4012_ = lean_box(v___x_4007_);
v___f_4013_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 32, 26);
lean_closure_set(v___f_4013_, 0, v_ctors_3975_);
lean_closure_set(v___f_4013_, 1, v_tail_3976_);
lean_closure_set(v___f_4013_, 2, v_params_3977_);
lean_closure_set(v___f_4013_, 3, v___x_3978_);
lean_closure_set(v___f_4013_, 4, v_numIndices_3979_);
lean_closure_set(v___f_4013_, 5, v___x_3980_);
lean_closure_set(v___f_4013_, 6, v___x_4003_);
lean_closure_set(v___f_4013_, 7, v___x_4010_);
lean_closure_set(v___f_4013_, 8, v___x_4011_);
lean_closure_set(v___f_4013_, 9, v___x_4012_);
lean_closure_set(v___f_4013_, 10, v_is_3973_);
lean_closure_set(v___f_4013_, 11, v___x_3972_);
lean_closure_set(v___f_4013_, 12, v___x_3971_);
lean_closure_set(v___f_4013_, 13, v___x_3981_);
lean_closure_set(v___f_4013_, 14, v___x_3982_);
lean_closure_set(v___f_4013_, 15, v___x_3983_);
lean_closure_set(v___f_4013_, 16, v___x_3984_);
lean_closure_set(v___f_4013_, 17, v_heq_3992_);
lean_closure_set(v___f_4013_, 18, v_val_3985_);
lean_closure_set(v___f_4013_, 19, v___x_3986_);
lean_closure_set(v___f_4013_, 20, v_declName_3987_);
lean_closure_set(v___f_4013_, 21, v_levelParams_3988_);
lean_closure_set(v___f_4013_, 22, v___x_3998_);
lean_closure_set(v___f_4013_, 23, v_numParams_3989_);
lean_closure_set(v___f_4013_, 24, v___x_3990_);
lean_closure_set(v___f_4013_, 25, v___x_3991_);
v___x_4014_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4015_ = 0;
v___x_4016_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4014_, v___x_4007_, v_a_4009_, v___f_4013_, v___x_4015_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
return v___x_4016_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref(v___x_4003_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v_heq_3992_);
lean_dec_ref(v___x_3990_);
lean_dec(v_numParams_3989_);
lean_dec(v_levelParams_3988_);
lean_dec(v_declName_3987_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_val_3985_);
lean_dec_ref(v___x_3984_);
lean_dec_ref(v___x_3983_);
lean_dec(v___x_3982_);
lean_dec(v___x_3981_);
lean_dec(v___x_3980_);
lean_dec(v_numIndices_3979_);
lean_dec(v___x_3978_);
lean_dec_ref(v_params_3977_);
lean_dec(v_tail_3976_);
lean_dec(v_ctors_3975_);
lean_dec_ref(v_is_3973_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v___x_3971_);
v_a_4017_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4008_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4008_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4025_ = _args[0];
lean_object* v___x_4026_ = _args[1];
lean_object* v_is_4027_ = _args[2];
lean_object* v_head_4028_ = _args[3];
lean_object* v_ctors_4029_ = _args[4];
lean_object* v_tail_4030_ = _args[5];
lean_object* v_params_4031_ = _args[6];
lean_object* v___x_4032_ = _args[7];
lean_object* v_numIndices_4033_ = _args[8];
lean_object* v___x_4034_ = _args[9];
lean_object* v___x_4035_ = _args[10];
lean_object* v___x_4036_ = _args[11];
lean_object* v___x_4037_ = _args[12];
lean_object* v___x_4038_ = _args[13];
lean_object* v_val_4039_ = _args[14];
lean_object* v___x_4040_ = _args[15];
lean_object* v_declName_4041_ = _args[16];
lean_object* v_levelParams_4042_ = _args[17];
lean_object* v_numParams_4043_ = _args[18];
lean_object* v___x_4044_ = _args[19];
lean_object* v___x_4045_ = _args[20];
lean_object* v_heq_4046_ = _args[21];
lean_object* v___y_4047_ = _args[22];
lean_object* v___y_4048_ = _args[23];
lean_object* v___y_4049_ = _args[24];
lean_object* v___y_4050_ = _args[25];
lean_object* v___y_4051_ = _args[26];
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4025_, v___x_4026_, v_is_4027_, v_head_4028_, v_ctors_4029_, v_tail_4030_, v_params_4031_, v___x_4032_, v_numIndices_4033_, v___x_4034_, v___x_4035_, v___x_4036_, v___x_4037_, v___x_4038_, v_val_4039_, v___x_4040_, v_declName_4041_, v_levelParams_4042_, v_numParams_4043_, v___x_4044_, v___x_4045_, v_heq_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4053_, lean_object* v_x1_4054_, lean_object* v_indName_4055_, lean_object* v_tail_4056_, lean_object* v_params_4057_, lean_object* v_is_4058_, lean_object* v___x_4059_, lean_object* v_head_4060_, lean_object* v_ctors_4061_, lean_object* v_numIndices_4062_, lean_object* v___x_4063_, lean_object* v___x_4064_, lean_object* v_val_4065_, lean_object* v_declName_4066_, lean_object* v_levelParams_4067_, lean_object* v_numParams_4068_, lean_object* v___x_4069_, lean_object* v___x_4070_, lean_object* v_x2_4071_, lean_object* v_x_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4078_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_4053_);
v___x_4079_ = lean_array_get_borrowed(v___x_4053_, v_x1_4054_, v___x_4078_);
v___x_4080_ = lean_array_get_borrowed(v___x_4053_, v_x2_4071_, v___x_4078_);
v___x_4081_ = l_mkCtorIdxName(v_indName_4055_);
lean_inc(v_tail_4056_);
v___x_4082_ = l_Lean_mkConst(v___x_4081_, v_tail_4056_);
lean_inc_ref(v_params_4057_);
v___x_4083_ = l_Array_append___redArg(v_params_4057_, v_is_4058_);
v___x_4084_ = lean_mk_empty_array_with_capacity(v___x_4059_);
lean_inc(v___x_4079_);
lean_inc_ref(v___x_4084_);
v___x_4085_ = lean_array_push(v___x_4084_, v___x_4079_);
lean_inc_ref(v___x_4083_);
v___x_4086_ = l_Array_append___redArg(v___x_4083_, v___x_4085_);
lean_inc_ref(v___x_4082_);
v___x_4087_ = l_Lean_mkAppN(v___x_4082_, v___x_4086_);
lean_dec_ref(v___x_4086_);
lean_inc(v___x_4080_);
lean_inc_ref(v___x_4084_);
v___x_4088_ = lean_array_push(v___x_4084_, v___x_4080_);
v___x_4089_ = l_Array_append___redArg(v___x_4083_, v___x_4088_);
v___x_4090_ = l_Lean_mkAppN(v___x_4082_, v___x_4089_);
lean_dec_ref(v___x_4089_);
lean_inc(v___y_4076_);
lean_inc_ref(v___y_4075_);
lean_inc(v___y_4074_);
lean_inc_ref(v___y_4073_);
v___x_4091_ = l_Lean_Meta_mkEq(v___x_4087_, v___x_4090_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___f_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref(v___x_4091_);
lean_inc(v___x_4080_);
lean_inc(v___x_4079_);
v___f_4093_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 27, 21);
lean_closure_set(v___f_4093_, 0, v___x_4079_);
lean_closure_set(v___f_4093_, 1, v___x_4080_);
lean_closure_set(v___f_4093_, 2, v_is_4058_);
lean_closure_set(v___f_4093_, 3, v_head_4060_);
lean_closure_set(v___f_4093_, 4, v_ctors_4061_);
lean_closure_set(v___f_4093_, 5, v_tail_4056_);
lean_closure_set(v___f_4093_, 6, v_params_4057_);
lean_closure_set(v___f_4093_, 7, v___x_4078_);
lean_closure_set(v___f_4093_, 8, v_numIndices_4062_);
lean_closure_set(v___f_4093_, 9, v___x_4059_);
lean_closure_set(v___f_4093_, 10, v___x_4063_);
lean_closure_set(v___f_4093_, 11, v___x_4064_);
lean_closure_set(v___f_4093_, 12, v___x_4085_);
lean_closure_set(v___f_4093_, 13, v___x_4088_);
lean_closure_set(v___f_4093_, 14, v_val_4065_);
lean_closure_set(v___f_4093_, 15, v___x_4084_);
lean_closure_set(v___f_4093_, 16, v_declName_4066_);
lean_closure_set(v___f_4093_, 17, v_levelParams_4067_);
lean_closure_set(v___f_4093_, 18, v_numParams_4068_);
lean_closure_set(v___f_4093_, 19, v___x_4069_);
lean_closure_set(v___f_4093_, 20, v___x_4070_);
v___x_4094_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4095_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4094_, v_a_4092_, v___f_4093_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
return v___x_4095_;
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec_ref(v___x_4088_);
lean_dec_ref(v___x_4085_);
lean_dec_ref(v___x_4084_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec_ref(v___x_4069_);
lean_dec(v_numParams_4068_);
lean_dec(v_levelParams_4067_);
lean_dec(v_declName_4066_);
lean_dec_ref(v_val_4065_);
lean_dec(v___x_4064_);
lean_dec(v___x_4063_);
lean_dec(v_numIndices_4062_);
lean_dec(v_ctors_4061_);
lean_dec(v_head_4060_);
lean_dec(v___x_4059_);
lean_dec_ref(v_is_4058_);
lean_dec_ref(v_params_4057_);
lean_dec(v_tail_4056_);
v_a_4096_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4091_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4091_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4104_ = _args[0];
lean_object* v_x1_4105_ = _args[1];
lean_object* v_indName_4106_ = _args[2];
lean_object* v_tail_4107_ = _args[3];
lean_object* v_params_4108_ = _args[4];
lean_object* v_is_4109_ = _args[5];
lean_object* v___x_4110_ = _args[6];
lean_object* v_head_4111_ = _args[7];
lean_object* v_ctors_4112_ = _args[8];
lean_object* v_numIndices_4113_ = _args[9];
lean_object* v___x_4114_ = _args[10];
lean_object* v___x_4115_ = _args[11];
lean_object* v_val_4116_ = _args[12];
lean_object* v_declName_4117_ = _args[13];
lean_object* v_levelParams_4118_ = _args[14];
lean_object* v_numParams_4119_ = _args[15];
lean_object* v___x_4120_ = _args[16];
lean_object* v___x_4121_ = _args[17];
lean_object* v_x2_4122_ = _args[18];
lean_object* v_x_4123_ = _args[19];
lean_object* v___y_4124_ = _args[20];
lean_object* v___y_4125_ = _args[21];
lean_object* v___y_4126_ = _args[22];
lean_object* v___y_4127_ = _args[23];
lean_object* v___y_4128_ = _args[24];
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4104_, v_x1_4105_, v_indName_4106_, v_tail_4107_, v_params_4108_, v_is_4109_, v___x_4110_, v_head_4111_, v_ctors_4112_, v_numIndices_4113_, v___x_4114_, v___x_4115_, v_val_4116_, v_declName_4117_, v_levelParams_4118_, v_numParams_4119_, v___x_4120_, v___x_4121_, v_x2_4122_, v_x_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec_ref(v_x_4123_);
lean_dec_ref(v_x2_4122_);
lean_dec_ref(v_x1_4105_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4130_, lean_object* v_indName_4131_, lean_object* v_tail_4132_, lean_object* v_params_4133_, lean_object* v_is_4134_, lean_object* v___x_4135_, lean_object* v_head_4136_, lean_object* v_ctors_4137_, lean_object* v_numIndices_4138_, lean_object* v___x_4139_, lean_object* v___x_4140_, lean_object* v_val_4141_, lean_object* v_declName_4142_, lean_object* v_levelParams_4143_, lean_object* v_numParams_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v_t_4147_, lean_object* v___x_4148_, lean_object* v_x1_4149_, lean_object* v_x_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___f_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; 
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 25, 18);
lean_closure_set(v___f_4156_, 0, v___x_4130_);
lean_closure_set(v___f_4156_, 1, v_x1_4149_);
lean_closure_set(v___f_4156_, 2, v_indName_4131_);
lean_closure_set(v___f_4156_, 3, v_tail_4132_);
lean_closure_set(v___f_4156_, 4, v_params_4133_);
lean_closure_set(v___f_4156_, 5, v_is_4134_);
lean_closure_set(v___f_4156_, 6, v___x_4135_);
lean_closure_set(v___f_4156_, 7, v_head_4136_);
lean_closure_set(v___f_4156_, 8, v_ctors_4137_);
lean_closure_set(v___f_4156_, 9, v_numIndices_4138_);
lean_closure_set(v___f_4156_, 10, v___x_4139_);
lean_closure_set(v___f_4156_, 11, v___x_4140_);
lean_closure_set(v___f_4156_, 12, v_val_4141_);
lean_closure_set(v___f_4156_, 13, v_declName_4142_);
lean_closure_set(v___f_4156_, 14, v_levelParams_4143_);
lean_closure_set(v___f_4156_, 15, v_numParams_4144_);
lean_closure_set(v___f_4156_, 16, v___x_4145_);
lean_closure_set(v___f_4156_, 17, v___x_4146_);
v___x_4157_ = 0;
v___x_4158_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4147_, v___x_4148_, v___f_4156_, v___x_4157_, v___x_4157_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4159_ = _args[0];
lean_object* v_indName_4160_ = _args[1];
lean_object* v_tail_4161_ = _args[2];
lean_object* v_params_4162_ = _args[3];
lean_object* v_is_4163_ = _args[4];
lean_object* v___x_4164_ = _args[5];
lean_object* v_head_4165_ = _args[6];
lean_object* v_ctors_4166_ = _args[7];
lean_object* v_numIndices_4167_ = _args[8];
lean_object* v___x_4168_ = _args[9];
lean_object* v___x_4169_ = _args[10];
lean_object* v_val_4170_ = _args[11];
lean_object* v_declName_4171_ = _args[12];
lean_object* v_levelParams_4172_ = _args[13];
lean_object* v_numParams_4173_ = _args[14];
lean_object* v___x_4174_ = _args[15];
lean_object* v___x_4175_ = _args[16];
lean_object* v_t_4176_ = _args[17];
lean_object* v___x_4177_ = _args[18];
lean_object* v_x1_4178_ = _args[19];
lean_object* v_x_4179_ = _args[20];
lean_object* v___y_4180_ = _args[21];
lean_object* v___y_4181_ = _args[22];
lean_object* v___y_4182_ = _args[23];
lean_object* v___y_4183_ = _args[24];
lean_object* v___y_4184_ = _args[25];
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4159_, v_indName_4160_, v_tail_4161_, v_params_4162_, v_is_4163_, v___x_4164_, v_head_4165_, v_ctors_4166_, v_numIndices_4167_, v___x_4168_, v___x_4169_, v_val_4170_, v_declName_4171_, v_levelParams_4172_, v_numParams_4173_, v___x_4174_, v___x_4175_, v_t_4176_, v___x_4177_, v_x1_4178_, v_x_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec_ref(v_x_4179_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4186_, lean_object* v_indName_4187_, lean_object* v_tail_4188_, lean_object* v_params_4189_, lean_object* v_head_4190_, lean_object* v_ctors_4191_, lean_object* v_numIndices_4192_, lean_object* v___x_4193_, lean_object* v___x_4194_, lean_object* v_val_4195_, lean_object* v_declName_4196_, lean_object* v_levelParams_4197_, lean_object* v_numParams_4198_, lean_object* v___x_4199_, lean_object* v___x_4200_, lean_object* v_is_4201_, lean_object* v_t_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___f_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; 
v___x_4208_ = lean_unsigned_to_nat(1u);
v___x_4209_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4202_);
v___f_4210_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 26, 19);
lean_closure_set(v___f_4210_, 0, v___x_4186_);
lean_closure_set(v___f_4210_, 1, v_indName_4187_);
lean_closure_set(v___f_4210_, 2, v_tail_4188_);
lean_closure_set(v___f_4210_, 3, v_params_4189_);
lean_closure_set(v___f_4210_, 4, v_is_4201_);
lean_closure_set(v___f_4210_, 5, v___x_4208_);
lean_closure_set(v___f_4210_, 6, v_head_4190_);
lean_closure_set(v___f_4210_, 7, v_ctors_4191_);
lean_closure_set(v___f_4210_, 8, v_numIndices_4192_);
lean_closure_set(v___f_4210_, 9, v___x_4193_);
lean_closure_set(v___f_4210_, 10, v___x_4194_);
lean_closure_set(v___f_4210_, 11, v_val_4195_);
lean_closure_set(v___f_4210_, 12, v_declName_4196_);
lean_closure_set(v___f_4210_, 13, v_levelParams_4197_);
lean_closure_set(v___f_4210_, 14, v_numParams_4198_);
lean_closure_set(v___f_4210_, 15, v___x_4199_);
lean_closure_set(v___f_4210_, 16, v___x_4200_);
lean_closure_set(v___f_4210_, 17, v_t_4202_);
lean_closure_set(v___f_4210_, 18, v___x_4209_);
v___x_4211_ = 0;
v___x_4212_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4202_, v___x_4209_, v___f_4210_, v___x_4211_, v___x_4211_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4213_ = _args[0];
lean_object* v_indName_4214_ = _args[1];
lean_object* v_tail_4215_ = _args[2];
lean_object* v_params_4216_ = _args[3];
lean_object* v_head_4217_ = _args[4];
lean_object* v_ctors_4218_ = _args[5];
lean_object* v_numIndices_4219_ = _args[6];
lean_object* v___x_4220_ = _args[7];
lean_object* v___x_4221_ = _args[8];
lean_object* v_val_4222_ = _args[9];
lean_object* v_declName_4223_ = _args[10];
lean_object* v_levelParams_4224_ = _args[11];
lean_object* v_numParams_4225_ = _args[12];
lean_object* v___x_4226_ = _args[13];
lean_object* v___x_4227_ = _args[14];
lean_object* v_is_4228_ = _args[15];
lean_object* v_t_4229_ = _args[16];
lean_object* v___y_4230_ = _args[17];
lean_object* v___y_4231_ = _args[18];
lean_object* v___y_4232_ = _args[19];
lean_object* v___y_4233_ = _args[20];
lean_object* v___y_4234_ = _args[21];
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4213_, v_indName_4214_, v_tail_4215_, v_params_4216_, v_head_4217_, v_ctors_4218_, v_numIndices_4219_, v___x_4220_, v___x_4221_, v_val_4222_, v_declName_4223_, v_levelParams_4224_, v_numParams_4225_, v___x_4226_, v___x_4227_, v_is_4228_, v_t_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4236_, lean_object* v_indName_4237_, lean_object* v_tail_4238_, lean_object* v_head_4239_, lean_object* v_ctors_4240_, lean_object* v_numIndices_4241_, lean_object* v___x_4242_, lean_object* v___x_4243_, lean_object* v_val_4244_, lean_object* v_declName_4245_, lean_object* v_levelParams_4246_, lean_object* v_numParams_4247_, lean_object* v___x_4248_, lean_object* v_params_4249_, lean_object* v_t_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___x_4256_; lean_object* v___f_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; 
v___x_4256_ = l_Lean_Expr_bindingBody_x21(v_t_4250_);
lean_inc_ref(v___x_4256_);
lean_inc(v_numIndices_4241_);
v___f_4257_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 22, 15);
lean_closure_set(v___f_4257_, 0, v___x_4236_);
lean_closure_set(v___f_4257_, 1, v_indName_4237_);
lean_closure_set(v___f_4257_, 2, v_tail_4238_);
lean_closure_set(v___f_4257_, 3, v_params_4249_);
lean_closure_set(v___f_4257_, 4, v_head_4239_);
lean_closure_set(v___f_4257_, 5, v_ctors_4240_);
lean_closure_set(v___f_4257_, 6, v_numIndices_4241_);
lean_closure_set(v___f_4257_, 7, v___x_4242_);
lean_closure_set(v___f_4257_, 8, v___x_4243_);
lean_closure_set(v___f_4257_, 9, v_val_4244_);
lean_closure_set(v___f_4257_, 10, v_declName_4245_);
lean_closure_set(v___f_4257_, 11, v_levelParams_4246_);
lean_closure_set(v___f_4257_, 12, v_numParams_4247_);
lean_closure_set(v___f_4257_, 13, v___x_4256_);
lean_closure_set(v___f_4257_, 14, v___x_4248_);
v___x_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4258_, 0, v_numIndices_4241_);
v___x_4259_ = 0;
v___x_4260_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4256_, v___x_4258_, v___f_4257_, v___x_4259_, v___x_4259_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4261_ = _args[0];
lean_object* v_indName_4262_ = _args[1];
lean_object* v_tail_4263_ = _args[2];
lean_object* v_head_4264_ = _args[3];
lean_object* v_ctors_4265_ = _args[4];
lean_object* v_numIndices_4266_ = _args[5];
lean_object* v___x_4267_ = _args[6];
lean_object* v___x_4268_ = _args[7];
lean_object* v_val_4269_ = _args[8];
lean_object* v_declName_4270_ = _args[9];
lean_object* v_levelParams_4271_ = _args[10];
lean_object* v_numParams_4272_ = _args[11];
lean_object* v___x_4273_ = _args[12];
lean_object* v_params_4274_ = _args[13];
lean_object* v_t_4275_ = _args[14];
lean_object* v___y_4276_ = _args[15];
lean_object* v___y_4277_ = _args[16];
lean_object* v___y_4278_ = _args[17];
lean_object* v___y_4279_ = _args[18];
lean_object* v___y_4280_ = _args[19];
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4261_, v_indName_4262_, v_tail_4263_, v_head_4264_, v_ctors_4265_, v_numIndices_4266_, v___x_4267_, v___x_4268_, v_val_4269_, v_declName_4270_, v_levelParams_4271_, v_numParams_4272_, v___x_4273_, v_params_4274_, v_t_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec_ref(v_t_4275_);
return v_res_4281_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4286_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4287_ = lean_unsigned_to_nat(58u);
v___x_4288_ = lean_unsigned_to_nat(142u);
v___x_4289_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4290_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4291_ = l_mkPanicMessageWithDecl(v___x_4290_, v___x_4289_, v___x_4288_, v___x_4287_, v___x_4286_);
return v___x_4291_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4292_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4293_ = lean_unsigned_to_nat(60u);
v___x_4294_ = lean_unsigned_to_nat(136u);
v___x_4295_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4296_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4297_ = l_mkPanicMessageWithDecl(v___x_4296_, v___x_4295_, v___x_4294_, v___x_4293_, v___x_4292_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4298_, lean_object* v_indName_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v___x_4305_; 
lean_inc_ref(v_a_4302_);
lean_inc(v_indName_4299_);
v___x_4305_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref(v___x_4305_);
if (lean_obj_tag(v_a_4306_) == 5)
{
lean_object* v_val_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_val_4307_ = lean_ctor_get(v_a_4306_, 0);
lean_inc_ref(v_val_4307_);
lean_dec_ref(v_a_4306_);
v___x_4308_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4298_);
v___x_4309_ = l_Lean_Name_append(v_declName_4298_, v___x_4308_);
lean_inc(v_a_4303_);
lean_inc_ref(v_a_4302_);
lean_inc(v_a_4301_);
lean_inc_ref(v_a_4300_);
lean_inc(v_indName_4299_);
lean_inc(v___x_4309_);
v___x_4310_ = l_Lean_mkCasesOnSameCtorHet(v___x_4309_, v_indName_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4344_; 
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; 
v_unused_4345_ = lean_ctor_get(v___x_4310_, 0);
lean_dec(v_unused_4345_);
v___x_4312_ = v___x_4310_;
v_isShared_4313_ = v_isSharedCheck_4344_;
goto v_resetjp_4311_;
}
else
{
lean_dec(v___x_4310_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4344_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_inc(v_indName_4299_);
v___x_4314_ = l_Lean_mkCasesOnName(v_indName_4299_);
lean_inc_ref(v_a_4302_);
v___x_4315_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4314_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v_levelParams_4317_; lean_object* v_type_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref(v___x_4315_);
v_levelParams_4317_ = lean_ctor_get(v_a_4316_, 1);
lean_inc(v_levelParams_4317_);
v_type_4318_ = lean_ctor_get(v_a_4316_, 2);
lean_inc_ref(v_type_4318_);
lean_dec(v_a_4316_);
v___x_4319_ = lean_box(0);
lean_inc(v_levelParams_4317_);
v___x_4320_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4317_, v___x_4319_);
if (lean_obj_tag(v___x_4320_) == 1)
{
lean_object* v_head_4321_; lean_object* v_tail_4322_; lean_object* v_numParams_4323_; lean_object* v_numIndices_4324_; lean_object* v_ctors_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; lean_object* v___x_4330_; 
v_head_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_head_4321_);
v_tail_4322_ = lean_ctor_get(v___x_4320_, 1);
lean_inc(v_tail_4322_);
v_numParams_4323_ = lean_ctor_get(v_val_4307_, 1);
lean_inc(v_numParams_4323_);
v_numIndices_4324_ = lean_ctor_get(v_val_4307_, 2);
lean_inc(v_numIndices_4324_);
v_ctors_4325_ = lean_ctor_get(v_val_4307_, 4);
lean_inc(v_ctors_4325_);
v___x_4326_ = l_Lean_instInhabitedExpr;
v___x_4327_ = lean_box(0);
lean_inc(v_numParams_4323_);
v___f_4328_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 20, 13);
lean_closure_set(v___f_4328_, 0, v___x_4326_);
lean_closure_set(v___f_4328_, 1, v_indName_4299_);
lean_closure_set(v___f_4328_, 2, v_tail_4322_);
lean_closure_set(v___f_4328_, 3, v_head_4321_);
lean_closure_set(v___f_4328_, 4, v_ctors_4325_);
lean_closure_set(v___f_4328_, 5, v_numIndices_4324_);
lean_closure_set(v___f_4328_, 6, v___x_4309_);
lean_closure_set(v___f_4328_, 7, v___x_4320_);
lean_closure_set(v___f_4328_, 8, v_val_4307_);
lean_closure_set(v___f_4328_, 9, v_declName_4298_);
lean_closure_set(v___f_4328_, 10, v_levelParams_4317_);
lean_closure_set(v___f_4328_, 11, v_numParams_4323_);
lean_closure_set(v___f_4328_, 12, v___x_4327_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 1);
lean_ctor_set(v___x_4312_, 0, v_numParams_4323_);
v___x_4330_ = v___x_4312_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_numParams_4323_);
v___x_4330_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
uint8_t v___x_4331_; lean_object* v___x_4332_; 
v___x_4331_ = 0;
v___x_4332_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4318_, v___x_4330_, v___f_4328_, v___x_4331_, v___x_4331_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
return v___x_4332_;
}
}
else
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
lean_dec(v___x_4320_);
lean_dec_ref(v_type_4318_);
lean_dec(v_levelParams_4317_);
lean_del_object(v___x_4312_);
lean_dec(v___x_4309_);
lean_dec_ref(v_val_4307_);
lean_dec(v_indName_4299_);
lean_dec(v_declName_4298_);
v___x_4334_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4335_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4334_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
return v___x_4335_;
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_del_object(v___x_4312_);
lean_dec(v___x_4309_);
lean_dec_ref(v_val_4307_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_indName_4299_);
lean_dec(v_declName_4298_);
v_a_4336_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4315_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4315_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
else
{
lean_dec(v___x_4309_);
lean_dec_ref(v_val_4307_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_indName_4299_);
lean_dec(v_declName_4298_);
return v___x_4310_;
}
}
else
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
lean_dec(v_a_4306_);
lean_dec(v_indName_4299_);
lean_dec(v_declName_4298_);
v___x_4346_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4347_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4346_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
return v___x_4347_;
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_indName_4299_);
lean_dec(v_declName_4298_);
v_a_4348_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4305_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4305_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4356_, lean_object* v_indName_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_mkCasesOnSameCtor(v_declName_4356_, v_indName_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4364_, lean_object* v_params_4365_, lean_object* v_motive_4366_, lean_object* v_as_4367_, lean_object* v_i_4368_, lean_object* v_j_4369_, lean_object* v_inv_4370_, lean_object* v_bs_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4364_, v_params_4365_, v_motive_4366_, v_as_4367_, v_i_4368_, v_j_4369_, v_bs_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4378_, lean_object* v_params_4379_, lean_object* v_motive_4380_, lean_object* v_as_4381_, lean_object* v_i_4382_, lean_object* v_j_4383_, lean_object* v_inv_4384_, lean_object* v_bs_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4378_, v_params_4379_, v_motive_4380_, v_as_4381_, v_i_4382_, v_j_4383_, v_inv_4384_, v_bs_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec_ref(v_as_4381_);
lean_dec_ref(v_params_4379_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4392_, lean_object* v_params_4393_, lean_object* v_a_4394_, lean_object* v_snd_4395_, lean_object* v_alts_4396_, lean_object* v_as_4397_, lean_object* v_i_4398_, lean_object* v_j_4399_, lean_object* v_inv_4400_, lean_object* v_bs_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4392_, v_params_4393_, v_a_4394_, v_snd_4395_, v_alts_4396_, v_as_4397_, v_i_4398_, v_j_4399_, v_bs_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4408_, lean_object* v_params_4409_, lean_object* v_a_4410_, lean_object* v_snd_4411_, lean_object* v_alts_4412_, lean_object* v_as_4413_, lean_object* v_i_4414_, lean_object* v_j_4415_, lean_object* v_inv_4416_, lean_object* v_bs_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4408_, v_params_4409_, v_a_4410_, v_snd_4411_, v_alts_4412_, v_as_4413_, v_i_4414_, v_j_4415_, v_inv_4416_, v_bs_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec_ref(v_as_4413_);
lean_dec_ref(v_params_4409_);
return v_res_4423_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
}
#ifdef __cplusplus
}
#endif
