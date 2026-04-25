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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object**);
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
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
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
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
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object* v_k_78_, lean_object* v_b_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
v___x_85_ = lean_apply_6(v_k_78_, v_b_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object* v_k_86_, lean_object* v_b_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(v_k_86_, v_b_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
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
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
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
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
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
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
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
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object* v_name_228_, lean_object* v_levelParams_229_, lean_object* v_type_230_, lean_object* v_value_231_, lean_object* v_hints_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; uint8_t v___y_237_; uint8_t v___y_244_; lean_object* v_env_247_; uint8_t v___x_248_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_env_247_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref_n(v_env_247_, 2);
lean_dec(v___x_235_);
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
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
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
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
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
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_15693__overap_448_; lean_object* v___x_449_; 
v___f_447_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15693__overap_448_ = lean_panic_fn_borrowed(v___f_447_, v_msg_441_);
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___x_449_ = lean_apply_5(v___x_15693__overap_448_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
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
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
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
uint8_t v_isZero_boxed_509_; uint8_t v___x_20783__boxed_510_; uint8_t v___x_20784__boxed_511_; lean_object* v_res_512_; 
v_isZero_boxed_509_ = lean_unbox(v_isZero_499_);
v___x_20783__boxed_510_ = lean_unbox(v___x_500_);
v___x_20784__boxed_511_ = lean_unbox(v___x_501_);
v_res_512_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_495_, v_alts_496_, v_j_497_, v_zs1_498_, v_isZero_boxed_509_, v___x_20783__boxed_510_, v___x_20784__boxed_511_, v_zs2_502_, v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_x_503_);
lean_dec_ref(v_zs2_502_);
lean_dec(v_j_497_);
lean_dec_ref(v_alts_496_);
lean_dec_ref(v___x_495_);
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
lean_dec_ref(v___x_543_);
return v___x_544_;
}
}
else
{
lean_dec(v_a_538_);
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
uint8_t v_isZero_boxed_589_; uint8_t v___x_20818__boxed_590_; uint8_t v___x_20819__boxed_591_; lean_object* v_res_592_; 
v_isZero_boxed_589_ = lean_unbox(v_isZero_570_);
v___x_20818__boxed_590_ = lean_unbox(v___x_571_);
v___x_20819__boxed_591_ = lean_unbox(v___x_572_);
v_res_592_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_567_, v_ism2_568_, v_motive_569_, v_isZero_boxed_589_, v___x_20818__boxed_590_, v___x_20819__boxed_591_, v_a_573_, v___f_574_, v_zs1_575_, v_val_576_, v___x_577_, v_indName_578_, v___x_579_, v___x_580_, v_params_581_, v___x_582_, v_h_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
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
uint8_t v_isZero_boxed_687_; uint8_t v___x_20949__boxed_688_; uint8_t v___x_20950__boxed_689_; lean_object* v_res_690_; 
v_isZero_boxed_687_ = lean_unbox(v_isZero_663_);
v___x_20949__boxed_688_ = lean_unbox(v___x_664_);
v___x_20950__boxed_689_ = lean_unbox(v___x_665_);
v_res_690_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_660_, v_alts_661_, v_j_662_, v_isZero_boxed_687_, v___x_20949__boxed_688_, v___x_20950__boxed_689_, v___x_666_, v___x_667_, v___x_668_, v_ism2_669_, v_motive_670_, v_a_671_, v_val_672_, v_indName_673_, v___x_674_, v___x_675_, v_params_676_, v___x_677_, v___x_678_, v___x_679_, v_zs1_680_, v_ctorRet1_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
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
lean_inc_n(v_a_737_, 2);
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
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
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
lean_dec_ref(v___x_819_);
return v___x_820_;
}
else
{
lean_dec(v_a_803_);
lean_dec(v_a_798_);
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
uint8_t v___x_21174__boxed_855_; uint8_t v___x_21175__boxed_856_; uint8_t v___x_21176__boxed_857_; lean_object* v_res_858_; 
v___x_21174__boxed_855_ = lean_unbox(v___x_833_);
v___x_21175__boxed_856_ = lean_unbox(v___x_834_);
v___x_21176__boxed_857_ = lean_unbox(v___x_835_);
v_res_858_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_829_, v___x_830_, v_a_831_, v_ism1_832_, v___x_21174__boxed_855_, v___x_21175__boxed_856_, v___x_21176__boxed_857_, v___x_836_, v_tail_837_, v_params_838_, v_alts_839_, v_numParams_840_, v_ism2_841_, v_val_842_, v_indName_843_, v___x_844_, v___x_845_, v___x_846_, v_name_847_, v___x_848_, v_heq_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
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
lean_inc_ref_n(v_params_861_, 2);
v___x_884_ = l_Array_append___redArg(v_params_861_, v_ism1_862_);
lean_inc_ref(v___x_883_);
v___x_885_ = l_Lean_mkAppN(v___x_883_, v___x_884_);
lean_dec_ref(v___x_884_);
v___x_886_ = l_Array_append___redArg(v_params_861_, v_ism2_863_);
v___x_887_ = l_Lean_mkAppN(v___x_883_, v___x_886_);
lean_dec_ref(v___x_886_);
lean_inc_ref(v___x_887_);
lean_inc_ref(v___x_885_);
v___x_888_ = l_Lean_Meta_mkEq(v___x_885_, v___x_887_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
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
uint8_t v___x_21301__boxed_921_; uint8_t v___x_21302__boxed_922_; uint8_t v___x_21303__boxed_923_; lean_object* v_res_924_; 
v___x_21301__boxed_921_ = lean_unbox(v___x_905_);
v___x_21302__boxed_922_ = lean_unbox(v___x_906_);
v___x_21303__boxed_923_ = lean_unbox(v___x_907_);
v_res_924_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_898_, v_tail_899_, v_params_900_, v_ism1_901_, v_ism2_902_, v_motive_903_, v___x_904_, v___x_21301__boxed_921_, v___x_21302__boxed_922_, v___x_21303__boxed_923_, v___x_908_, v_numParams_909_, v_val_910_, v___x_911_, v___x_912_, v_name_913_, v___x_914_, v_alts_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_snd_925_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_933_, v_x_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_x_934_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_941_, size_t v_i_942_, lean_object* v_bs_943_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_lt(v_i_942_, v_sz_941_);
if (v___x_944_ == 0)
{
return v_bs_943_;
}
else
{
lean_object* v_v_945_; lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_961_; 
v_v_945_ = lean_array_uget(v_bs_943_, v_i_942_);
v_fst_946_ = lean_ctor_get(v_v_945_, 0);
v_snd_947_ = lean_ctor_get(v_v_945_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_v_945_);
if (v_isSharedCheck_961_ == 0)
{
v___x_949_ = v_v_945_;
v_isShared_950_ = v_isSharedCheck_961_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_snd_947_);
lean_inc(v_fst_946_);
lean_dec(v_v_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_961_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v_bs_x27_952_; lean_object* v___f_953_; lean_object* v___x_955_; 
v___x_951_ = lean_unsigned_to_nat(0u);
v_bs_x27_952_ = lean_array_uset(v_bs_943_, v_i_942_, v___x_951_);
v___f_953_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_953_, 0, v_snd_947_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___f_953_);
v___x_955_ = v___x_949_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___f_953_);
v___x_955_ = v_reuseFailAlloc_960_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_942_, v___x_956_);
v___x_958_ = lean_array_uset(v_bs_x27_952_, v_i_942_, v___x_955_);
v_i_942_ = v___x_957_;
v_bs_943_ = v___x_958_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_962_, lean_object* v_i_963_, lean_object* v_bs_964_){
_start:
{
size_t v_sz_boxed_965_; size_t v_i_boxed_966_; lean_object* v_res_967_; 
v_sz_boxed_965_ = lean_unbox_usize(v_sz_962_);
lean_dec(v_sz_962_);
v_i_boxed_966_ = lean_unbox_usize(v_i_963_);
lean_dec(v_i_963_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_965_, v_i_boxed_966_, v_bs_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_968_, lean_object* v_a_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_20204__overap_976_; lean_object* v___x_977_; 
v___x_975_ = l_Lean_instInhabitedExpr;
v___x_20204__overap_976_ = l_instInhabitedOfMonad___redArg(v___x_968_, v___x_975_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
v___x_977_ = lean_apply_5(v___x_20204__overap_976_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, lean_box(0));
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_978_, lean_object* v_a_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_978_, v_a_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_a_979_);
return v_res_985_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_instMonadEIO(lean_box(0));
return v___x_986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_988_ = l_StateRefT_x27_instMonad___redArg(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_993_, lean_object* v_declInfos_994_, lean_object* v_k_995_, lean_object* v_kind_996_, lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
uint8_t v_kind_boxed_1003_; lean_object* v_res_1004_; 
v_kind_boxed_1003_ = lean_unbox(v_kind_996_);
v_res_1004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_993_, v_declInfos_994_, v_k_995_, v_kind_boxed_1003_, v_x_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1005_, lean_object* v_k_1006_, uint8_t v_kind_1007_, lean_object* v_acc_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v_toApplicative_1015_; lean_object* v_toFunctor_1016_; lean_object* v_toSeq_1017_; lean_object* v_toSeqLeft_1018_; lean_object* v_toSeqRight_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_toApplicative_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1080_; 
v___x_1014_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1015_ = lean_ctor_get(v___x_1014_, 0);
v_toFunctor_1016_ = lean_ctor_get(v_toApplicative_1015_, 0);
v_toSeq_1017_ = lean_ctor_get(v_toApplicative_1015_, 2);
v_toSeqLeft_1018_ = lean_ctor_get(v_toApplicative_1015_, 3);
v_toSeqRight_1019_ = lean_ctor_get(v_toApplicative_1015_, 4);
v___f_1020_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1021_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1016_, 2);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toFunctor_1016_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toFunctor_1016_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___f_1022_);
lean_ctor_set(v___x_1024_, 1, v___f_1023_);
lean_inc(v_toSeqRight_1019_);
v___f_1025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1025_, 0, v_toSeqRight_1019_);
lean_inc(v_toSeqLeft_1018_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toSeqLeft_1018_);
lean_inc(v_toSeq_1017_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toSeq_1017_);
v___x_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___f_1020_);
lean_ctor_set(v___x_1028_, 2, v___f_1027_);
lean_ctor_set(v___x_1028_, 3, v___f_1026_);
lean_ctor_set(v___x_1028_, 4, v___f_1025_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___f_1021_);
v___x_1030_ = l_StateRefT_x27_instMonad___redArg(v___x_1029_);
v_toApplicative_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1030_, 1);
lean_dec(v_unused_1081_);
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1080_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_toApplicative_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1080_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_toFunctor_1035_; lean_object* v_toSeq_1036_; lean_object* v_toSeqLeft_1037_; lean_object* v_toSeqRight_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1078_; 
v_toFunctor_1035_ = lean_ctor_get(v_toApplicative_1031_, 0);
v_toSeq_1036_ = lean_ctor_get(v_toApplicative_1031_, 2);
v_toSeqLeft_1037_ = lean_ctor_get(v_toApplicative_1031_, 3);
v_toSeqRight_1038_ = lean_ctor_get(v_toApplicative_1031_, 4);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_toApplicative_1031_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_dec(v_unused_1079_);
v___x_1040_ = v_toApplicative_1031_;
v_isShared_1041_ = v_isSharedCheck_1078_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_toSeqRight_1038_);
lean_inc(v_toSeqLeft_1037_);
lean_inc(v_toSeq_1036_);
lean_inc(v_toFunctor_1035_);
lean_dec(v_toApplicative_1031_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1078_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___x_1051_; 
v___f_1042_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1043_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1035_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toFunctor_1035_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toFunctor_1035_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___f_1044_);
lean_ctor_set(v___x_1046_, 1, v___f_1045_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toSeqRight_1038_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeqLeft_1037_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeq_1036_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 4, v___f_1047_);
lean_ctor_set(v___x_1040_, 3, v___f_1048_);
lean_ctor_set(v___x_1040_, 2, v___f_1049_);
lean_ctor_set(v___x_1040_, 1, v___f_1042_);
lean_ctor_set(v___x_1040_, 0, v___x_1046_);
v___x_1051_ = v___x_1040_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___f_1042_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___f_1048_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___f_1047_);
v___x_1051_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___f_1043_);
lean_ctor_set(v___x_1033_, 0, v___x_1051_);
v___x_1053_ = v___x_1033_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_1043_);
v___x_1053_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_array_get_size(v_acc_1008_);
v___x_1055_ = lean_array_get_size(v_declInfos_1005_);
v___x_1056_ = lean_nat_dec_lt(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref(v___x_1053_);
lean_dec_ref(v_declInfos_1005_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
v___x_1057_ = lean_apply_6(v_k_1006_, v_acc_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1057_;
}
else
{
lean_object* v___f_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_snd_1066_; lean_object* v_fst_1067_; lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; 
v___f_1058_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1058_, 0, v___x_1053_);
v___x_1059_ = lean_box(0);
v___x_1060_ = 0;
v___f_1061_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1061_, 0, v___f_1058_);
v___x_1062_ = lean_box(v___x_1060_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___f_1061_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1059_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_array_get(v___x_1064_, v_declInfos_1005_, v___x_1054_);
lean_dec_ref(v___x_1064_);
v_snd_1066_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_snd_1066_);
v_fst_1067_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_fst_1067_);
lean_dec(v___x_1065_);
v_fst_1068_ = lean_ctor_get(v_snd_1066_, 0);
lean_inc(v_fst_1068_);
v_snd_1069_ = lean_ctor_get(v_snd_1066_, 1);
lean_inc(v_snd_1069_);
lean_dec(v_snd_1066_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc_ref(v_acc_1008_);
v___x_1070_ = lean_apply_6(v_snd_1069_, v_acc_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___f_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = lean_box(v_kind_1007_);
v___f_1073_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1073_, 0, v_acc_1008_);
lean_closure_set(v___f_1073_, 1, v_declInfos_1005_);
lean_closure_set(v___f_1073_, 2, v_k_1006_);
lean_closure_set(v___f_1073_, 3, v___x_1072_);
v___x_1074_ = lean_unbox(v_fst_1068_);
lean_dec(v_fst_1068_);
v___x_1075_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1067_, v___x_1074_, v_a_1071_, v___f_1073_, v_kind_1007_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1075_;
}
else
{
lean_dec(v_fst_1068_);
lean_dec(v_fst_1067_);
lean_dec_ref(v_acc_1008_);
lean_dec_ref(v_k_1006_);
lean_dec_ref(v_declInfos_1005_);
return v___x_1070_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1082_, lean_object* v_declInfos_1083_, lean_object* v_k_1084_, uint8_t v_kind_1085_, lean_object* v_x_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_array_push(v_acc_1082_, v_x_1086_);
v___x_1093_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1083_, v_k_1084_, v_kind_1085_, v___x_1092_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1094_, lean_object* v_k_1095_, lean_object* v_kind_1096_, lean_object* v_acc_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v_kind_boxed_1103_; lean_object* v_res_1104_; 
v_kind_boxed_1103_ = lean_unbox(v_kind_1096_);
v_res_1104_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1094_, v_k_1095_, v_kind_boxed_1103_, v_acc_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1107_, lean_object* v_k_1108_, uint8_t v_kind_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1107_, v_k_1108_, v_kind_1109_, v___x_1115_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1117_, lean_object* v_k_1118_, lean_object* v_kind_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v_kind_boxed_1125_; lean_object* v_res_1126_; 
v_kind_boxed_1125_ = lean_unbox(v_kind_1119_);
v_res_1126_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1117_, v_k_1118_, v_kind_boxed_1125_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1127_, size_t v_i_1128_, lean_object* v_bs_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_lt(v_i_1128_, v_sz_1127_);
if (v___x_1130_ == 0)
{
return v_bs_1129_;
}
else
{
lean_object* v_v_1131_; lean_object* v_fst_1132_; lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1149_; 
v_v_1131_ = lean_array_uget(v_bs_1129_, v_i_1128_);
v_fst_1132_ = lean_ctor_get(v_v_1131_, 0);
v_snd_1133_ = lean_ctor_get(v_v_1131_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_v_1131_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1135_ = v_v_1131_;
v_isShared_1136_ = v_isSharedCheck_1149_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_inc(v_fst_1132_);
lean_dec(v_v_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1149_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v_bs_x27_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
v_bs_x27_1138_ = lean_array_uset(v_bs_1129_, v_i_1128_, v___x_1137_);
v___x_1139_ = 0;
v___x_1140_ = lean_box(v___x_1139_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1140_);
v___x_1142_ = v___x_1135_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_snd_1133_);
v___x_1142_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_fst_1132_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1128_, v___x_1144_);
v___x_1146_ = lean_array_uset(v_bs_x27_1138_, v_i_1128_, v___x_1143_);
v_i_1128_ = v___x_1145_;
v_bs_1129_ = v___x_1146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_bs_1152_){
_start:
{
size_t v_sz_boxed_1153_; size_t v_i_boxed_1154_; lean_object* v_res_1155_; 
v_sz_boxed_1153_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1154_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1153_, v_i_boxed_1154_, v_bs_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1156_, lean_object* v_k_1157_, uint8_t v_kind_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_1164_; size_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_sz_1164_ = lean_array_size(v_declInfos_1156_);
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1164_, v___x_1165_, v_declInfos_1156_);
v___x_1167_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1166_, v_k_1157_, v_kind_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1168_, lean_object* v_k_1169_, lean_object* v_kind_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v_kind_boxed_1176_; lean_object* v_res_1177_; 
v_kind_boxed_1176_ = lean_unbox(v_kind_1170_);
v_res_1177_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1168_, v_k_1169_, v_kind_boxed_1176_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1178_, lean_object* v_k_1179_, uint8_t v_kind_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
size_t v_sz_1186_; size_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_sz_1186_ = lean_array_size(v_declInfos_1178_);
v___x_1187_ = ((size_t)0ULL);
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1186_, v___x_1187_, v_declInfos_1178_);
v___x_1189_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1188_, v_k_1179_, v_kind_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1190_, lean_object* v_k_1191_, lean_object* v_kind_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_kind_boxed_1198_; lean_object* v_res_1199_; 
v_kind_boxed_1198_ = lean_unbox(v_kind_1192_);
v_res_1199_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1190_, v_k_1191_, v_kind_boxed_1198_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1201_, lean_object* v_dummy_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v_motive_1206_, lean_object* v_zs1_1207_, uint8_t v_isZero_1208_, uint8_t v___x_1209_, uint8_t v___x_1210_, lean_object* v___x_1211_, lean_object* v_j_1212_, lean_object* v_zs2_1213_, lean_object* v_ctorRet2_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
v___x_1220_ = lean_whnf(v_ctorRet2_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v_nargs_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = l_Lean_mkAppN(v___x_1201_, v_zs2_1213_);
v_nargs_1223_ = l_Lean_Expr_getAppNumArgs(v_a_1221_);
lean_inc(v_nargs_1223_);
v___x_1224_ = lean_mk_array(v_nargs_1223_, v_dummy_1202_);
v___x_1225_ = lean_nat_sub(v_nargs_1223_, v___x_1203_);
lean_dec(v_nargs_1223_);
v___x_1226_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1221_, v___x_1224_, v___x_1225_);
v___x_1227_ = lean_array_get_size(v___x_1226_);
v___x_1228_ = l_Array_toSubarray___redArg(v___x_1226_, v___x_1204_, v___x_1227_);
v___x_1229_ = l_Subarray_copy___redArg(v___x_1228_);
v___x_1230_ = lean_array_push(v___x_1229_, v___x_1222_);
v___x_1231_ = l_Array_append___redArg(v___x_1205_, v___x_1230_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = l_Lean_mkAppN(v_motive_1206_, v___x_1231_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = l_Array_append___redArg(v_zs1_1207_, v_zs2_1213_);
v___x_1234_ = l_Lean_Meta_mkForallFVars(v___x_1233_, v___x_1232_, v_isZero_1208_, v___x_1209_, v___x_1209_, v___x_1210_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec_ref(v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1254_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1254_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1254_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___y_1240_; 
if (lean_obj_tag(v___x_1211_) == 1)
{
lean_object* v_str_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_str_1245_ = lean_ctor_get(v___x_1211_, 1);
lean_inc_ref(v_str_1245_);
lean_dec_ref(v___x_1211_);
v___x_1246_ = lean_box(0);
v___x_1247_ = l_Lean_Name_str___override(v___x_1246_, v_str_1245_);
v___y_1240_ = v___x_1247_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v___x_1211_);
v___x_1248_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1249_ = lean_nat_add(v_j_1212_, v___x_1203_);
v___x_1250_ = l_Nat_reprFast(v___x_1249_);
v___x_1251_ = lean_string_append(v___x_1248_, v___x_1250_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = lean_box(0);
v___x_1253_ = l_Lean_Name_str___override(v___x_1252_, v___x_1251_);
v___y_1240_ = v___x_1253_;
goto v___jp_1239_;
}
v___jp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___y_1240_);
lean_ctor_set(v___x_1241_, 1, v_a_1235_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1241_);
v___x_1243_ = v___x_1237_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v___x_1211_);
v_a_1255_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1234_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1234_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v___x_1211_);
lean_dec_ref(v_zs1_1207_);
lean_dec_ref(v_motive_1206_);
lean_dec_ref(v___x_1205_);
lean_dec(v___x_1204_);
lean_dec_ref(v_dummy_1202_);
lean_dec_ref(v___x_1201_);
v_a_1263_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1220_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1220_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1271_ = _args[0];
lean_object* v_dummy_1272_ = _args[1];
lean_object* v___x_1273_ = _args[2];
lean_object* v___x_1274_ = _args[3];
lean_object* v___x_1275_ = _args[4];
lean_object* v_motive_1276_ = _args[5];
lean_object* v_zs1_1277_ = _args[6];
lean_object* v_isZero_1278_ = _args[7];
lean_object* v___x_1279_ = _args[8];
lean_object* v___x_1280_ = _args[9];
lean_object* v___x_1281_ = _args[10];
lean_object* v_j_1282_ = _args[11];
lean_object* v_zs2_1283_ = _args[12];
lean_object* v_ctorRet2_1284_ = _args[13];
lean_object* v___y_1285_ = _args[14];
lean_object* v___y_1286_ = _args[15];
lean_object* v___y_1287_ = _args[16];
lean_object* v___y_1288_ = _args[17];
lean_object* v___y_1289_ = _args[18];
_start:
{
uint8_t v_isZero_boxed_1290_; uint8_t v___x_21737__boxed_1291_; uint8_t v___x_21738__boxed_1292_; lean_object* v_res_1293_; 
v_isZero_boxed_1290_ = lean_unbox(v_isZero_1278_);
v___x_21737__boxed_1291_ = lean_unbox(v___x_1279_);
v___x_21738__boxed_1292_ = lean_unbox(v___x_1280_);
v_res_1293_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1271_, v_dummy_1272_, v___x_1273_, v___x_1274_, v___x_1275_, v_motive_1276_, v_zs1_1277_, v_isZero_boxed_1290_, v___x_21737__boxed_1291_, v___x_21738__boxed_1292_, v___x_1281_, v_j_1282_, v_zs2_1283_, v_ctorRet2_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v_zs2_1283_);
lean_dec(v_j_1282_);
lean_dec(v___x_1273_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_motive_1297_, uint8_t v_isZero_1298_, uint8_t v___x_1299_, uint8_t v___x_1300_, lean_object* v___x_1301_, lean_object* v_j_1302_, lean_object* v_a_1303_, lean_object* v_zs1_1304_, lean_object* v_ctorRet1_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
v___x_1311_ = lean_whnf(v_ctorRet1_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v_dummy_1314_; lean_object* v_nargs_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1311_);
lean_inc_ref(v___x_1294_);
v___x_1313_ = l_Lean_mkAppN(v___x_1294_, v_zs1_1304_);
v_dummy_1314_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1315_ = l_Lean_Expr_getAppNumArgs(v_a_1312_);
lean_inc(v_nargs_1315_);
v___x_1316_ = lean_mk_array(v_nargs_1315_, v_dummy_1314_);
v___x_1317_ = lean_nat_sub(v_nargs_1315_, v___x_1295_);
lean_dec(v_nargs_1315_);
v___x_1318_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1312_, v___x_1316_, v___x_1317_);
v___x_1319_ = lean_array_get_size(v___x_1318_);
lean_inc(v___x_1296_);
v___x_1320_ = l_Array_toSubarray___redArg(v___x_1318_, v___x_1296_, v___x_1319_);
v___x_1321_ = l_Subarray_copy___redArg(v___x_1320_);
v___x_1322_ = lean_array_push(v___x_1321_, v___x_1313_);
v___x_1323_ = lean_box(v_isZero_1298_);
v___x_1324_ = lean_box(v___x_1299_);
v___x_1325_ = lean_box(v___x_1300_);
v___f_1326_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1326_, 0, v___x_1294_);
lean_closure_set(v___f_1326_, 1, v_dummy_1314_);
lean_closure_set(v___f_1326_, 2, v___x_1295_);
lean_closure_set(v___f_1326_, 3, v___x_1296_);
lean_closure_set(v___f_1326_, 4, v___x_1322_);
lean_closure_set(v___f_1326_, 5, v_motive_1297_);
lean_closure_set(v___f_1326_, 6, v_zs1_1304_);
lean_closure_set(v___f_1326_, 7, v___x_1323_);
lean_closure_set(v___f_1326_, 8, v___x_1324_);
lean_closure_set(v___f_1326_, 9, v___x_1325_);
lean_closure_set(v___f_1326_, 10, v___x_1301_);
lean_closure_set(v___f_1326_, 11, v_j_1302_);
v___x_1327_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1303_, v___f_1326_, v_isZero_1298_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1327_;
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_zs1_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_j_1302_);
lean_dec(v___x_1301_);
lean_dec_ref(v_motive_1297_);
lean_dec(v___x_1296_);
lean_dec(v___x_1295_);
lean_dec_ref(v___x_1294_);
v_a_1328_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1311_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1311_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1336_ = _args[0];
lean_object* v___x_1337_ = _args[1];
lean_object* v___x_1338_ = _args[2];
lean_object* v_motive_1339_ = _args[3];
lean_object* v_isZero_1340_ = _args[4];
lean_object* v___x_1341_ = _args[5];
lean_object* v___x_1342_ = _args[6];
lean_object* v___x_1343_ = _args[7];
lean_object* v_j_1344_ = _args[8];
lean_object* v_a_1345_ = _args[9];
lean_object* v_zs1_1346_ = _args[10];
lean_object* v_ctorRet1_1347_ = _args[11];
lean_object* v___y_1348_ = _args[12];
lean_object* v___y_1349_ = _args[13];
lean_object* v___y_1350_ = _args[14];
lean_object* v___y_1351_ = _args[15];
lean_object* v___y_1352_ = _args[16];
_start:
{
uint8_t v_isZero_boxed_1353_; uint8_t v___x_21875__boxed_1354_; uint8_t v___x_21876__boxed_1355_; lean_object* v_res_1356_; 
v_isZero_boxed_1353_ = lean_unbox(v_isZero_1340_);
v___x_21875__boxed_1354_ = lean_unbox(v___x_1341_);
v___x_21876__boxed_1355_ = lean_unbox(v___x_1342_);
v_res_1356_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1336_, v___x_1337_, v___x_1338_, v_motive_1339_, v_isZero_boxed_1353_, v___x_21875__boxed_1354_, v___x_21876__boxed_1355_, v___x_1343_, v_j_1344_, v_a_1345_, v_zs1_1346_, v_ctorRet1_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1357_, lean_object* v_params_1358_, lean_object* v___x_1359_, lean_object* v_motive_1360_, lean_object* v_as_1361_, lean_object* v_i_1362_, lean_object* v_j_1363_, lean_object* v_bs_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_zero_1370_; uint8_t v_isZero_1371_; 
v_zero_1370_ = lean_unsigned_to_nat(0u);
v_isZero_1371_ = lean_nat_dec_eq(v_i_1362_, v_zero_1370_);
if (v_isZero_1371_ == 1)
{
lean_object* v___x_1372_; 
lean_dec(v_j_1363_);
lean_dec(v_i_1362_);
lean_dec_ref(v_motive_1360_);
lean_dec(v___x_1359_);
lean_dec(v_tail_1357_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_bs_1364_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1373_ = lean_array_fget_borrowed(v_as_1361_, v_j_1363_);
lean_inc(v_tail_1357_);
lean_inc(v___x_1373_);
v___x_1374_ = l_Lean_mkConst(v___x_1373_, v_tail_1357_);
v___x_1375_ = l_Lean_mkAppN(v___x_1374_, v_params_1358_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc_ref(v___x_1375_);
v___x_1376_ = lean_infer_type(v___x_1375_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; uint8_t v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_n(v_a_1377_, 2);
lean_dec_ref(v___x_1376_);
v___x_1378_ = 1;
v___x_1379_ = 1;
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_box(v_isZero_1371_);
v___x_1382_ = lean_box(v___x_1378_);
v___x_1383_ = lean_box(v___x_1379_);
lean_inc(v_j_1363_);
lean_inc(v___x_1373_);
lean_inc_ref(v_motive_1360_);
lean_inc(v___x_1359_);
v___f_1384_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1384_, 0, v___x_1375_);
lean_closure_set(v___f_1384_, 1, v___x_1380_);
lean_closure_set(v___f_1384_, 2, v___x_1359_);
lean_closure_set(v___f_1384_, 3, v_motive_1360_);
lean_closure_set(v___f_1384_, 4, v___x_1381_);
lean_closure_set(v___f_1384_, 5, v___x_1382_);
lean_closure_set(v___f_1384_, 6, v___x_1383_);
lean_closure_set(v___f_1384_, 7, v___x_1373_);
lean_closure_set(v___f_1384_, 8, v_j_1363_);
lean_closure_set(v___f_1384_, 9, v_a_1377_);
v___x_1385_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1377_, v___f_1384_, v_isZero_1371_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_n_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
v_n_1387_ = lean_nat_sub(v_i_1362_, v___x_1380_);
lean_dec(v_i_1362_);
v___x_1388_ = lean_nat_add(v_j_1363_, v___x_1380_);
lean_dec(v_j_1363_);
v___x_1389_ = lean_array_push(v_bs_1364_, v_a_1386_);
v_i_1362_ = v_n_1387_;
v_j_1363_ = v___x_1388_;
v_bs_1364_ = v___x_1389_;
goto _start;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v_bs_1364_);
lean_dec(v_j_1363_);
lean_dec(v_i_1362_);
lean_dec_ref(v_motive_1360_);
lean_dec(v___x_1359_);
lean_dec(v_tail_1357_);
v_a_1391_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1385_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1385_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_bs_1364_);
lean_dec(v_j_1363_);
lean_dec(v_i_1362_);
lean_dec_ref(v_motive_1360_);
lean_dec(v___x_1359_);
lean_dec(v_tail_1357_);
v_a_1399_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1376_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1376_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1407_, lean_object* v_params_1408_, lean_object* v___x_1409_, lean_object* v_motive_1410_, lean_object* v_as_1411_, lean_object* v_i_1412_, lean_object* v_j_1413_, lean_object* v_bs_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1407_, v_params_1408_, v___x_1409_, v_motive_1410_, v_as_1411_, v_i_1412_, v_j_1413_, v_bs_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_as_1411_);
lean_dec_ref(v_params_1408_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1421_, lean_object* v_tail_1422_, lean_object* v_params_1423_, lean_object* v_numParams_1424_, lean_object* v_indName_1425_, lean_object* v_ism1_1426_, lean_object* v_ism2_1427_, lean_object* v___x_1428_, uint8_t v___x_1429_, uint8_t v___x_1430_, uint8_t v___x_1431_, lean_object* v_val_1432_, lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v_name_1435_, lean_object* v___x_1436_, lean_object* v_motive_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1443_ = lean_array_mk(v_ctors_1421_);
v___x_1444_ = lean_array_get_size(v___x_1443_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_mk_empty_array_with_capacity(v___x_1444_);
lean_inc_ref(v_motive_1437_);
lean_inc(v_numParams_1424_);
lean_inc(v_tail_1422_);
v___x_1447_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1422_, v_params_1423_, v_numParams_1424_, v_motive_1437_, v___x_1443_, v___x_1444_, v___x_1445_, v___x_1446_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___f_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v___x_1447_);
v___x_1449_ = lean_box(v___x_1429_);
v___x_1450_ = lean_box(v___x_1430_);
v___x_1451_ = lean_box(v___x_1431_);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1452_, 0, v_indName_1425_);
lean_closure_set(v___f_1452_, 1, v_tail_1422_);
lean_closure_set(v___f_1452_, 2, v_params_1423_);
lean_closure_set(v___f_1452_, 3, v_ism1_1426_);
lean_closure_set(v___f_1452_, 4, v_ism2_1427_);
lean_closure_set(v___f_1452_, 5, v_motive_1437_);
lean_closure_set(v___f_1452_, 6, v___x_1428_);
lean_closure_set(v___f_1452_, 7, v___x_1449_);
lean_closure_set(v___f_1452_, 8, v___x_1450_);
lean_closure_set(v___f_1452_, 9, v___x_1451_);
lean_closure_set(v___f_1452_, 10, v___x_1443_);
lean_closure_set(v___f_1452_, 11, v_numParams_1424_);
lean_closure_set(v___f_1452_, 12, v_val_1432_);
lean_closure_set(v___f_1452_, 13, v___x_1433_);
lean_closure_set(v___f_1452_, 14, v___x_1434_);
lean_closure_set(v___f_1452_, 15, v_name_1435_);
lean_closure_set(v___f_1452_, 16, v___x_1436_);
v___x_1453_ = 0;
v___x_1454_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1448_, v___f_1452_, v___x_1453_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1454_;
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v___x_1443_);
lean_dec_ref(v_motive_1437_);
lean_dec(v___x_1436_);
lean_dec(v_name_1435_);
lean_dec(v___x_1434_);
lean_dec(v___x_1433_);
lean_dec_ref(v_val_1432_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v_ism2_1427_);
lean_dec_ref(v_ism1_1426_);
lean_dec(v_indName_1425_);
lean_dec(v_numParams_1424_);
lean_dec_ref(v_params_1423_);
lean_dec(v_tail_1422_);
v_a_1455_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1447_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1447_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1463_ = _args[0];
lean_object* v_tail_1464_ = _args[1];
lean_object* v_params_1465_ = _args[2];
lean_object* v_numParams_1466_ = _args[3];
lean_object* v_indName_1467_ = _args[4];
lean_object* v_ism1_1468_ = _args[5];
lean_object* v_ism2_1469_ = _args[6];
lean_object* v___x_1470_ = _args[7];
lean_object* v___x_1471_ = _args[8];
lean_object* v___x_1472_ = _args[9];
lean_object* v___x_1473_ = _args[10];
lean_object* v_val_1474_ = _args[11];
lean_object* v___x_1475_ = _args[12];
lean_object* v___x_1476_ = _args[13];
lean_object* v_name_1477_ = _args[14];
lean_object* v___x_1478_ = _args[15];
lean_object* v_motive_1479_ = _args[16];
lean_object* v___y_1480_ = _args[17];
lean_object* v___y_1481_ = _args[18];
lean_object* v___y_1482_ = _args[19];
lean_object* v___y_1483_ = _args[20];
lean_object* v___y_1484_ = _args[21];
_start:
{
uint8_t v___x_22048__boxed_1485_; uint8_t v___x_22049__boxed_1486_; uint8_t v___x_22050__boxed_1487_; lean_object* v_res_1488_; 
v___x_22048__boxed_1485_ = lean_unbox(v___x_1471_);
v___x_22049__boxed_1486_ = lean_unbox(v___x_1472_);
v___x_22050__boxed_1487_ = lean_unbox(v___x_1473_);
v_res_1488_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1463_, v_tail_1464_, v_params_1465_, v_numParams_1466_, v_indName_1467_, v_ism1_1468_, v_ism2_1469_, v___x_1470_, v___x_22048__boxed_1485_, v___x_22049__boxed_1486_, v___x_22050__boxed_1487_, v_val_1474_, v___x_1475_, v___x_1476_, v_name_1477_, v___x_1478_, v_motive_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1492_, lean_object* v_head_1493_, lean_object* v_ctors_1494_, lean_object* v_tail_1495_, lean_object* v_params_1496_, lean_object* v_numParams_1497_, lean_object* v_indName_1498_, lean_object* v_val_1499_, lean_object* v___x_1500_, lean_object* v___x_1501_, lean_object* v_name_1502_, lean_object* v___x_1503_, lean_object* v_ism2_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; uint8_t v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
lean_inc_ref(v_ism1_1492_);
v___x_1511_ = l_Array_append___redArg(v_ism1_1492_, v_ism2_1504_);
v___x_1512_ = l_Lean_mkSort(v_head_1493_);
v___x_1513_ = 0;
v___x_1514_ = 1;
v___x_1515_ = 1;
v___x_1516_ = l_Lean_Meta_mkForallFVars(v___x_1511_, v___x_1512_, v___x_1513_, v___x_1514_, v___x_1514_, v___x_1515_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = lean_box(v___x_1513_);
v___x_1519_ = lean_box(v___x_1514_);
v___x_1520_ = lean_box(v___x_1515_);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1521_, 0, v_ctors_1494_);
lean_closure_set(v___f_1521_, 1, v_tail_1495_);
lean_closure_set(v___f_1521_, 2, v_params_1496_);
lean_closure_set(v___f_1521_, 3, v_numParams_1497_);
lean_closure_set(v___f_1521_, 4, v_indName_1498_);
lean_closure_set(v___f_1521_, 5, v_ism1_1492_);
lean_closure_set(v___f_1521_, 6, v_ism2_1504_);
lean_closure_set(v___f_1521_, 7, v___x_1511_);
lean_closure_set(v___f_1521_, 8, v___x_1518_);
lean_closure_set(v___f_1521_, 9, v___x_1519_);
lean_closure_set(v___f_1521_, 10, v___x_1520_);
lean_closure_set(v___f_1521_, 11, v_val_1499_);
lean_closure_set(v___f_1521_, 12, v___x_1500_);
lean_closure_set(v___f_1521_, 13, v___x_1501_);
lean_closure_set(v___f_1521_, 14, v_name_1502_);
lean_closure_set(v___f_1521_, 15, v___x_1503_);
v___x_1522_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1523_ = 0;
v___x_1524_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1522_, v___x_1515_, v_a_1517_, v___f_1521_, v___x_1523_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1524_;
}
else
{
lean_dec_ref(v___x_1511_);
lean_dec_ref(v_ism2_1504_);
lean_dec(v___x_1503_);
lean_dec(v_name_1502_);
lean_dec(v___x_1501_);
lean_dec(v___x_1500_);
lean_dec_ref(v_val_1499_);
lean_dec(v_indName_1498_);
lean_dec(v_numParams_1497_);
lean_dec_ref(v_params_1496_);
lean_dec(v_tail_1495_);
lean_dec(v_ctors_1494_);
lean_dec_ref(v_ism1_1492_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1525_ = _args[0];
lean_object* v_head_1526_ = _args[1];
lean_object* v_ctors_1527_ = _args[2];
lean_object* v_tail_1528_ = _args[3];
lean_object* v_params_1529_ = _args[4];
lean_object* v_numParams_1530_ = _args[5];
lean_object* v_indName_1531_ = _args[6];
lean_object* v_val_1532_ = _args[7];
lean_object* v___x_1533_ = _args[8];
lean_object* v___x_1534_ = _args[9];
lean_object* v_name_1535_ = _args[10];
lean_object* v___x_1536_ = _args[11];
lean_object* v_ism2_1537_ = _args[12];
lean_object* v_x_1538_ = _args[13];
lean_object* v___y_1539_ = _args[14];
lean_object* v___y_1540_ = _args[15];
lean_object* v___y_1541_ = _args[16];
lean_object* v___y_1542_ = _args[17];
lean_object* v___y_1543_ = _args[18];
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1525_, v_head_1526_, v_ctors_1527_, v_tail_1528_, v_params_1529_, v_numParams_1530_, v_indName_1531_, v_val_1532_, v___x_1533_, v___x_1534_, v_name_1535_, v___x_1536_, v_ism2_1537_, v_x_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v_x_1538_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1545_, lean_object* v_ctors_1546_, lean_object* v_tail_1547_, lean_object* v_params_1548_, lean_object* v_numParams_1549_, lean_object* v_indName_1550_, lean_object* v_val_1551_, lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v_name_1554_, lean_object* v___x_1555_, lean_object* v_t_1556_, lean_object* v___x_1557_, lean_object* v_ism1_1558_, lean_object* v_x_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___f_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; 
v___f_1565_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1565_, 0, v_ism1_1558_);
lean_closure_set(v___f_1565_, 1, v_head_1545_);
lean_closure_set(v___f_1565_, 2, v_ctors_1546_);
lean_closure_set(v___f_1565_, 3, v_tail_1547_);
lean_closure_set(v___f_1565_, 4, v_params_1548_);
lean_closure_set(v___f_1565_, 5, v_numParams_1549_);
lean_closure_set(v___f_1565_, 6, v_indName_1550_);
lean_closure_set(v___f_1565_, 7, v_val_1551_);
lean_closure_set(v___f_1565_, 8, v___x_1552_);
lean_closure_set(v___f_1565_, 9, v___x_1553_);
lean_closure_set(v___f_1565_, 10, v_name_1554_);
lean_closure_set(v___f_1565_, 11, v___x_1555_);
v___x_1566_ = 0;
v___x_1567_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1556_, v___x_1557_, v___f_1565_, v___x_1566_, v___x_1566_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1568_ = _args[0];
lean_object* v_ctors_1569_ = _args[1];
lean_object* v_tail_1570_ = _args[2];
lean_object* v_params_1571_ = _args[3];
lean_object* v_numParams_1572_ = _args[4];
lean_object* v_indName_1573_ = _args[5];
lean_object* v_val_1574_ = _args[6];
lean_object* v___x_1575_ = _args[7];
lean_object* v___x_1576_ = _args[8];
lean_object* v_name_1577_ = _args[9];
lean_object* v___x_1578_ = _args[10];
lean_object* v_t_1579_ = _args[11];
lean_object* v___x_1580_ = _args[12];
lean_object* v_ism1_1581_ = _args[13];
lean_object* v_x_1582_ = _args[14];
lean_object* v___y_1583_ = _args[15];
lean_object* v___y_1584_ = _args[16];
lean_object* v___y_1585_ = _args[17];
lean_object* v___y_1586_ = _args[18];
lean_object* v___y_1587_ = _args[19];
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1568_, v_ctors_1569_, v_tail_1570_, v_params_1571_, v_numParams_1572_, v_indName_1573_, v_val_1574_, v___x_1575_, v___x_1576_, v_name_1577_, v___x_1578_, v_t_1579_, v___x_1580_, v_ism1_1581_, v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v_x_1582_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1589_, lean_object* v___x_1590_, lean_object* v_head_1591_, lean_object* v_ctors_1592_, lean_object* v_tail_1593_, lean_object* v_params_1594_, lean_object* v_numParams_1595_, lean_object* v_indName_1596_, lean_object* v_val_1597_, lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v_name_1600_, lean_object* v_x_1601_, lean_object* v_t_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___f_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1608_ = lean_nat_add(v_numIndices_1589_, v___x_1590_);
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_inc_ref(v___x_1609_);
lean_inc_ref(v_t_1602_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1610_, 0, v_head_1591_);
lean_closure_set(v___f_1610_, 1, v_ctors_1592_);
lean_closure_set(v___f_1610_, 2, v_tail_1593_);
lean_closure_set(v___f_1610_, 3, v_params_1594_);
lean_closure_set(v___f_1610_, 4, v_numParams_1595_);
lean_closure_set(v___f_1610_, 5, v_indName_1596_);
lean_closure_set(v___f_1610_, 6, v_val_1597_);
lean_closure_set(v___f_1610_, 7, v___x_1598_);
lean_closure_set(v___f_1610_, 8, v___x_1599_);
lean_closure_set(v___f_1610_, 9, v_name_1600_);
lean_closure_set(v___f_1610_, 10, v___x_1590_);
lean_closure_set(v___f_1610_, 11, v_t_1602_);
lean_closure_set(v___f_1610_, 12, v___x_1609_);
v___x_1611_ = 0;
v___x_1612_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1602_, v___x_1609_, v___f_1610_, v___x_1611_, v___x_1611_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1613_ = _args[0];
lean_object* v___x_1614_ = _args[1];
lean_object* v_head_1615_ = _args[2];
lean_object* v_ctors_1616_ = _args[3];
lean_object* v_tail_1617_ = _args[4];
lean_object* v_params_1618_ = _args[5];
lean_object* v_numParams_1619_ = _args[6];
lean_object* v_indName_1620_ = _args[7];
lean_object* v_val_1621_ = _args[8];
lean_object* v___x_1622_ = _args[9];
lean_object* v___x_1623_ = _args[10];
lean_object* v_name_1624_ = _args[11];
lean_object* v_x_1625_ = _args[12];
lean_object* v_t_1626_ = _args[13];
lean_object* v___y_1627_ = _args[14];
lean_object* v___y_1628_ = _args[15];
lean_object* v___y_1629_ = _args[16];
lean_object* v___y_1630_ = _args[17];
lean_object* v___y_1631_ = _args[18];
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1613_, v___x_1614_, v_head_1615_, v_ctors_1616_, v_tail_1617_, v_params_1618_, v_numParams_1619_, v_indName_1620_, v_val_1621_, v___x_1622_, v___x_1623_, v_name_1624_, v_x_1625_, v_t_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v_x_1625_);
lean_dec(v_numIndices_1613_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1635_, lean_object* v_head_1636_, lean_object* v_ctors_1637_, lean_object* v_tail_1638_, lean_object* v_numParams_1639_, lean_object* v_indName_1640_, lean_object* v_val_1641_, lean_object* v___x_1642_, lean_object* v___x_1643_, lean_object* v_name_1644_, lean_object* v_params_1645_, lean_object* v_t_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1652_ = lean_unsigned_to_nat(1u);
v___f_1653_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1653_, 0, v_numIndices_1635_);
lean_closure_set(v___f_1653_, 1, v___x_1652_);
lean_closure_set(v___f_1653_, 2, v_head_1636_);
lean_closure_set(v___f_1653_, 3, v_ctors_1637_);
lean_closure_set(v___f_1653_, 4, v_tail_1638_);
lean_closure_set(v___f_1653_, 5, v_params_1645_);
lean_closure_set(v___f_1653_, 6, v_numParams_1639_);
lean_closure_set(v___f_1653_, 7, v_indName_1640_);
lean_closure_set(v___f_1653_, 8, v_val_1641_);
lean_closure_set(v___f_1653_, 9, v___x_1642_);
lean_closure_set(v___f_1653_, 10, v___x_1643_);
lean_closure_set(v___f_1653_, 11, v_name_1644_);
v___x_1654_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1655_ = 0;
v___x_1656_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1646_, v___x_1654_, v___f_1653_, v___x_1655_, v___x_1655_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1657_ = _args[0];
lean_object* v_head_1658_ = _args[1];
lean_object* v_ctors_1659_ = _args[2];
lean_object* v_tail_1660_ = _args[3];
lean_object* v_numParams_1661_ = _args[4];
lean_object* v_indName_1662_ = _args[5];
lean_object* v_val_1663_ = _args[6];
lean_object* v___x_1664_ = _args[7];
lean_object* v___x_1665_ = _args[8];
lean_object* v_name_1666_ = _args[9];
lean_object* v_params_1667_ = _args[10];
lean_object* v_t_1668_ = _args[11];
lean_object* v___y_1669_ = _args[12];
lean_object* v___y_1670_ = _args[13];
lean_object* v___y_1671_ = _args[14];
lean_object* v___y_1672_ = _args[15];
lean_object* v___y_1673_ = _args[16];
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1657_, v_head_1658_, v_ctors_1659_, v_tail_1660_, v_numParams_1661_, v_indName_1662_, v_val_1663_, v___x_1664_, v___x_1665_, v_name_1666_, v_params_1667_, v_t_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1675_, lean_object* v_declName_1676_, lean_object* v_levelParams_1677_, uint8_t v___x_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; 
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc_ref(v_a_1675_);
v___x_1684_ = lean_infer_type(v_a_1675_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = lean_box(1);
v___x_1687_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1676_, v_levelParams_1677_, v_a_1685_, v_a_1675_, v___x_1686_, v___y_1682_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 1);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_addDecl(v___x_1693_, v___x_1678_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_levelParams_1677_);
lean_dec(v_declName_1676_);
lean_dec_ref(v_a_1675_);
v_a_1697_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1684_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1684_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1705_, lean_object* v_declName_1706_, lean_object* v_levelParams_1707_, lean_object* v___x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_22340__boxed_1714_; lean_object* v_res_1715_; 
v___x_22340__boxed_1714_ = lean_unbox(v___x_1708_);
v_res_1715_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1705_, v_declName_1706_, v_levelParams_1707_, v___x_22340__boxed_1714_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
if (lean_obj_tag(v_a_1716_) == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = l_List_reverse___redArg(v_a_1717_);
return v___x_1718_;
}
else
{
lean_object* v_head_1719_; lean_object* v_tail_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1729_; 
v_head_1719_ = lean_ctor_get(v_a_1716_, 0);
v_tail_1720_ = lean_ctor_get(v_a_1716_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1722_ = v_a_1716_;
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_tail_1720_);
lean_inc(v_head_1719_);
lean_dec(v_a_1716_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = l_Lean_mkLevelParam(v_head_1719_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v_a_1717_);
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_a_1717_);
v___x_1726_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
v_a_1716_ = v_tail_1720_;
v_a_1717_ = v___x_1726_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v_env_1737_; lean_object* v___x_1738_; lean_object* v_mctx_1739_; lean_object* v_lctx_1740_; lean_object* v_options_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1736_ = lean_st_ref_get(v___y_1734_);
v_env_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_ref(v_env_1737_);
lean_dec(v___x_1736_);
v___x_1738_ = lean_st_ref_get(v___y_1732_);
v_mctx_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_mctx_1739_);
lean_dec(v___x_1738_);
v_lctx_1740_ = lean_ctor_get(v___y_1731_, 2);
v_options_1741_ = lean_ctor_get(v___y_1733_, 2);
lean_inc_ref(v_options_1741_);
lean_inc_ref(v_lctx_1740_);
v___x_1742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1742_, 0, v_env_1737_);
lean_ctor_set(v___x_1742_, 1, v_mctx_1739_);
lean_ctor_set(v___x_1742_, 2, v_lctx_1740_);
lean_ctor_set(v___x_1742_, 3, v_options_1741_);
v___x_1743_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_msgData_1730_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_ref_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v_ref_1758_ = lean_ctor_get(v___y_1755_, 5);
v___x_1759_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc(v_ref_1758_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v_ref_1758_);
lean_ctor_set(v___x_1764_, 1, v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_fileName_1783_; lean_object* v_fileMap_1784_; lean_object* v_options_1785_; lean_object* v_currRecDepth_1786_; lean_object* v_maxRecDepth_1787_; lean_object* v_ref_1788_; lean_object* v_currNamespace_1789_; lean_object* v_openDecls_1790_; lean_object* v_initHeartbeats_1791_; lean_object* v_maxHeartbeats_1792_; lean_object* v_quotContext_1793_; lean_object* v_currMacroScope_1794_; uint8_t v_diag_1795_; lean_object* v_cancelTk_x3f_1796_; uint8_t v_suppressElabErrors_1797_; lean_object* v_inheritedTraceOptions_1798_; lean_object* v_ref_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_fileName_1783_ = lean_ctor_get(v___y_1780_, 0);
v_fileMap_1784_ = lean_ctor_get(v___y_1780_, 1);
v_options_1785_ = lean_ctor_get(v___y_1780_, 2);
v_currRecDepth_1786_ = lean_ctor_get(v___y_1780_, 3);
v_maxRecDepth_1787_ = lean_ctor_get(v___y_1780_, 4);
v_ref_1788_ = lean_ctor_get(v___y_1780_, 5);
v_currNamespace_1789_ = lean_ctor_get(v___y_1780_, 6);
v_openDecls_1790_ = lean_ctor_get(v___y_1780_, 7);
v_initHeartbeats_1791_ = lean_ctor_get(v___y_1780_, 8);
v_maxHeartbeats_1792_ = lean_ctor_get(v___y_1780_, 9);
v_quotContext_1793_ = lean_ctor_get(v___y_1780_, 10);
v_currMacroScope_1794_ = lean_ctor_get(v___y_1780_, 11);
v_diag_1795_ = lean_ctor_get_uint8(v___y_1780_, sizeof(void*)*14);
v_cancelTk_x3f_1796_ = lean_ctor_get(v___y_1780_, 12);
v_suppressElabErrors_1797_ = lean_ctor_get_uint8(v___y_1780_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1798_ = lean_ctor_get(v___y_1780_, 13);
v_ref_1799_ = l_Lean_replaceRef(v_ref_1776_, v_ref_1788_);
lean_inc_ref(v_inheritedTraceOptions_1798_);
lean_inc(v_cancelTk_x3f_1796_);
lean_inc(v_currMacroScope_1794_);
lean_inc(v_quotContext_1793_);
lean_inc(v_maxHeartbeats_1792_);
lean_inc(v_initHeartbeats_1791_);
lean_inc(v_openDecls_1790_);
lean_inc(v_currNamespace_1789_);
lean_inc(v_maxRecDepth_1787_);
lean_inc(v_currRecDepth_1786_);
lean_inc_ref(v_options_1785_);
lean_inc_ref(v_fileMap_1784_);
lean_inc_ref(v_fileName_1783_);
v___x_1800_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1800_, 0, v_fileName_1783_);
lean_ctor_set(v___x_1800_, 1, v_fileMap_1784_);
lean_ctor_set(v___x_1800_, 2, v_options_1785_);
lean_ctor_set(v___x_1800_, 3, v_currRecDepth_1786_);
lean_ctor_set(v___x_1800_, 4, v_maxRecDepth_1787_);
lean_ctor_set(v___x_1800_, 5, v_ref_1799_);
lean_ctor_set(v___x_1800_, 6, v_currNamespace_1789_);
lean_ctor_set(v___x_1800_, 7, v_openDecls_1790_);
lean_ctor_set(v___x_1800_, 8, v_initHeartbeats_1791_);
lean_ctor_set(v___x_1800_, 9, v_maxHeartbeats_1792_);
lean_ctor_set(v___x_1800_, 10, v_quotContext_1793_);
lean_ctor_set(v___x_1800_, 11, v_currMacroScope_1794_);
lean_ctor_set(v___x_1800_, 12, v_cancelTk_x3f_1796_);
lean_ctor_set(v___x_1800_, 13, v_inheritedTraceOptions_1798_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*14, v_diag_1795_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*14 + 1, v_suppressElabErrors_1797_);
v___x_1801_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1777_, v___y_1778_, v___y_1779_, v___x_1800_, v___y_1781_);
lean_dec_ref(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1802_, lean_object* v_msg_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1802_, v_msg_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_ref_1802_);
return v_res_1809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
lean_ctor_set(v___x_1815_, 2, v___x_1814_);
lean_ctor_set(v___x_1815_, 3, v___x_1814_);
lean_ctor_set(v___x_1815_, 4, v___x_1813_);
lean_ctor_set(v___x_1815_, 5, v___x_1813_);
lean_ctor_set(v___x_1815_, 6, v___x_1813_);
lean_ctor_set(v___x_1815_, 7, v___x_1813_);
lean_ctor_set(v___x_1815_, 8, v___x_1813_);
lean_ctor_set(v___x_1815_, 9, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(32u);
v___x_1817_ = lean_mk_empty_array_with_capacity(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = ((size_t)5ULL);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_unsigned_to_nat(32u);
v___x_1822_ = lean_mk_empty_array_with_capacity(v___x_1821_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1824_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
lean_ctor_set(v___x_1824_, 2, v___x_1820_);
lean_ctor_set(v___x_1824_, 3, v___x_1820_);
lean_ctor_set_usize(v___x_1824_, 4, v___x_1819_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_box(1);
v___x_1826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1825_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1850_, lean_object* v_declHint_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v_env_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_st_ref_get(v___y_1852_);
v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc_ref(v_env_1855_);
lean_dec(v___x_1854_);
v___x_1856_ = l_Lean_Name_isAnonymous(v_declHint_1851_);
if (v___x_1856_ == 0)
{
uint8_t v_isExporting_1857_; 
v_isExporting_1857_ = lean_ctor_get_uint8(v_env_1855_, sizeof(void*)*8);
if (v_isExporting_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_msg_1850_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
lean_inc_ref(v_env_1855_);
v___x_1859_ = l_Lean_Environment_setExporting(v_env_1855_, v___x_1856_);
lean_inc(v_declHint_1851_);
lean_inc_ref(v___x_1859_);
v___x_1860_ = l_Lean_Environment_contains(v___x_1859_, v_declHint_1851_, v_isExporting_1857_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v___x_1859_);
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_msg_1850_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v_c_1867_; lean_object* v___x_1868_; 
v___x_1862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1864_ = l_Lean_Options_empty;
v___x_1865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1859_);
lean_ctor_set(v___x_1865_, 1, v___x_1862_);
lean_ctor_set(v___x_1865_, 2, v___x_1863_);
lean_ctor_set(v___x_1865_, 3, v___x_1864_);
lean_inc(v_declHint_1851_);
v___x_1866_ = l_Lean_MessageData_ofConstName(v_declHint_1851_, v___x_1856_);
v_c_1867_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1867_, 0, v___x_1865_);
lean_ctor_set(v_c_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1855_, v_declHint_1851_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v_c_1867_);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_MessageData_note(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_msg_1850_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v_val_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1911_; 
v_val_1876_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1878_ = v___x_1868_;
v_isShared_1879_ = v_isSharedCheck_1911_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_val_1876_);
lean_dec(v___x_1868_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1911_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_mod_1883_; uint8_t v___x_1884_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = l_Lean_Environment_header(v_env_1855_);
lean_dec_ref(v_env_1855_);
v___x_1882_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1881_);
v_mod_1883_ = lean_array_get(v___x_1880_, v___x_1882_, v_val_1876_);
lean_dec(v_val_1876_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_isPrivateName(v_declHint_1851_);
lean_dec(v_declHint_1851_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v_c_1867_);
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_MessageData_ofName(v_mod_1883_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_MessageData_note(v___x_1892_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_msg_1850_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1894_);
v___x_1896_ = v___x_1878_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_c_1867_);
v___x_1900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = l_Lean_MessageData_ofName(v_mod_1883_);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_MessageData_note(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_msg_1850_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1907_);
v___x_1909_ = v___x_1878_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_msg_1850_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1913_, lean_object* v_declHint_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1913_, v_declHint_1914_, v___y_1915_);
lean_dec(v___y_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1918_, lean_object* v_declHint_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1935_; 
v___x_1925_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1918_, v_declHint_1919_, v___y_1923_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1935_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1935_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = l_Lean_unknownIdentifierMessageTag;
v___x_1931_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v_a_1926_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1936_, lean_object* v_declHint_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1936_, v_declHint_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1944_, lean_object* v_msg_1945_, lean_object* v_declHint_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v_a_1953_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1945_, v_declHint_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1944_, v_a_1953_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1955_, lean_object* v_msg_1956_, lean_object* v_declHint_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1955_, v_msg_1956_, v_declHint_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_ref_1955_);
return v_res_1963_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1970_, lean_object* v_constName_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1977_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1978_ = 0;
lean_inc(v_constName_1971_);
v___x_1979_ = l_Lean_MessageData_ofConstName(v_constName_1971_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1970_, v___x_1982_, v_constName_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1984_, lean_object* v_constName_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1984_, v_constName_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v_ref_1984_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_ref_1998_; lean_object* v___x_1999_; 
v_ref_1998_ = lean_ctor_get(v___y_1995_, 5);
v___x_1999_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1998_, v_constName_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_env_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = lean_st_ref_get(v___y_2011_);
v_env_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2014_);
lean_dec(v___x_2013_);
v___x_2015_ = 0;
lean_inc(v_constName_2007_);
v___x_2016_ = l_Lean_Environment_findConstVal_x3f(v_env_2014_, v_constName_2007_, v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2017_;
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_constName_2007_);
v_val_2018_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 0);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_val_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2033_, uint8_t v_s_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v_env_2039_; lean_object* v_nextMacroScope_2040_; lean_object* v_ngen_2041_; lean_object* v_auxDeclNGen_2042_; lean_object* v_traceState_2043_; lean_object* v_messages_2044_; lean_object* v_infoState_2045_; lean_object* v_snapshotTasks_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2075_; 
v___x_2038_ = lean_st_ref_take(v___y_2036_);
v_env_2039_ = lean_ctor_get(v___x_2038_, 0);
v_nextMacroScope_2040_ = lean_ctor_get(v___x_2038_, 1);
v_ngen_2041_ = lean_ctor_get(v___x_2038_, 2);
v_auxDeclNGen_2042_ = lean_ctor_get(v___x_2038_, 3);
v_traceState_2043_ = lean_ctor_get(v___x_2038_, 4);
v_messages_2044_ = lean_ctor_get(v___x_2038_, 6);
v_infoState_2045_ = lean_ctor_get(v___x_2038_, 7);
v_snapshotTasks_2046_ = lean_ctor_get(v___x_2038_, 8);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2038_, 5);
lean_dec(v_unused_2076_);
v___x_2048_ = v___x_2038_;
v_isShared_2049_ = v_isSharedCheck_2075_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_snapshotTasks_2046_);
lean_inc(v_infoState_2045_);
lean_inc(v_messages_2044_);
lean_inc(v_traceState_2043_);
lean_inc(v_auxDeclNGen_2042_);
lean_inc(v_ngen_2041_);
lean_inc(v_nextMacroScope_2040_);
lean_inc(v_env_2039_);
lean_dec(v___x_2038_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2075_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2050_ = 0;
v___x_2051_ = lean_box(0);
v___x_2052_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2039_, v_declName_2033_, v_s_2034_, v___x_2050_, v___x_2051_);
v___x_2053_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 5, v___x_2053_);
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2055_ = v___x_2048_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_nextMacroScope_2040_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_ngen_2041_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_auxDeclNGen_2042_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_traceState_2043_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v_messages_2044_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_infoState_2045_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_snapshotTasks_2046_);
v___x_2055_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_mctx_2058_; lean_object* v_zetaDeltaFVarIds_2059_; lean_object* v_postponed_2060_; lean_object* v_diag_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
v___x_2056_ = lean_st_ref_set(v___y_2036_, v___x_2055_);
v___x_2057_ = lean_st_ref_take(v___y_2035_);
v_mctx_2058_ = lean_ctor_get(v___x_2057_, 0);
v_zetaDeltaFVarIds_2059_ = lean_ctor_get(v___x_2057_, 2);
v_postponed_2060_ = lean_ctor_get(v___x_2057_, 3);
v_diag_2061_ = lean_ctor_get(v___x_2057_, 4);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2057_, 1);
lean_dec(v_unused_2073_);
v___x_2063_ = v___x_2057_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_diag_2061_);
lean_inc(v_postponed_2060_);
lean_inc(v_zetaDeltaFVarIds_2059_);
lean_inc(v_mctx_2058_);
lean_dec(v___x_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_mctx_2058_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_zetaDeltaFVarIds_2059_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_postponed_2060_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_diag_2061_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_st_ref_set(v___y_2035_, v___x_2067_);
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2077_, lean_object* v_s_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v_s_boxed_2082_; lean_object* v_res_2083_; 
v_s_boxed_2082_ = lean_unbox(v_s_2078_);
v_res_2083_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2077_, v_s_boxed_2082_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec(v___y_2079_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = 0;
v___x_2091_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2084_, v___x_2090_, v___y_2086_, v___y_2088_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2107_ = l_Lean_stringToMessageData(v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2108_, lean_object* v_declName_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2115_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2116_ = l_Lean_MessageData_ofName(v_attrName_2108_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = 0;
v___x_2121_ = l_Lean_MessageData_ofConstName(v_declName_2109_, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2119_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2124_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2126_, lean_object* v_declName_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2126_, v_declName_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2140_, lean_object* v_declName_2141_, lean_object* v_asyncPrefix_x3f_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___y_2149_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2142_) == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_MessageData_nil;
v___y_2149_ = v___x_2162_;
goto v___jp_2148_;
}
else
{
lean_object* v_val_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_val_2163_ = lean_ctor_get(v_asyncPrefix_x3f_2142_, 0);
lean_inc(v_val_2163_);
lean_dec_ref(v_asyncPrefix_x3f_2142_);
v___x_2164_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2165_ = l_Lean_MessageData_ofName(v_val_2163_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___y_2149_ = v___x_2168_;
goto v___jp_2148_;
}
v___jp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2150_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2151_ = l_Lean_MessageData_ofName(v_attrName_2140_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = 0;
v___x_2156_ = l_Lean_MessageData_ofConstName(v_declName_2141_, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___y_2149_);
v___x_2161_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2160_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2169_, lean_object* v_declName_2170_, lean_object* v_asyncPrefix_x3f_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2169_, v_declName_2170_, v_asyncPrefix_x3f_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2178_, lean_object* v_decl_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___x_2228_; lean_object* v_env_2229_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___x_2244_; 
v___x_2228_ = lean_st_ref_get(v___y_2183_);
v_env_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_env_2229_);
lean_dec(v___x_2228_);
v___x_2244_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2229_, v_decl_2179_);
if (lean_obj_tag(v___x_2244_) == 0)
{
v___y_2231_ = v___y_2180_;
v___y_2232_ = v___y_2181_;
v___y_2233_ = v___y_2182_;
v___y_2234_ = v___y_2183_;
goto v___jp_2230_;
}
else
{
lean_object* v_attr_2245_; lean_object* v_toAttributeImplCore_2246_; lean_object* v_name_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_env_2229_);
v_attr_2245_ = lean_ctor_get(v_attr_2178_, 0);
lean_inc_ref(v_attr_2245_);
lean_dec_ref(v_attr_2178_);
v_toAttributeImplCore_2246_ = lean_ctor_get(v_attr_2245_, 0);
lean_inc_ref(v_toAttributeImplCore_2246_);
lean_dec_ref(v_attr_2245_);
v_name_2247_ = lean_ctor_get(v_toAttributeImplCore_2246_, 1);
lean_inc(v_name_2247_);
lean_dec_ref(v_toAttributeImplCore_2246_);
v___x_2248_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2247_, v_decl_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2248_;
}
v___jp_2185_:
{
lean_object* v___x_2188_; lean_object* v_ext_2189_; lean_object* v_toEnvExtension_2190_; lean_object* v_env_2191_; lean_object* v_nextMacroScope_2192_; lean_object* v_ngen_2193_; lean_object* v_auxDeclNGen_2194_; lean_object* v_traceState_2195_; lean_object* v_messages_2196_; lean_object* v_infoState_2197_; lean_object* v_snapshotTasks_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2226_; 
v___x_2188_ = lean_st_ref_take(v___y_2187_);
v_ext_2189_ = lean_ctor_get(v_attr_2178_, 1);
lean_inc_ref(v_ext_2189_);
lean_dec_ref(v_attr_2178_);
v_toEnvExtension_2190_ = lean_ctor_get(v_ext_2189_, 0);
v_env_2191_ = lean_ctor_get(v___x_2188_, 0);
v_nextMacroScope_2192_ = lean_ctor_get(v___x_2188_, 1);
v_ngen_2193_ = lean_ctor_get(v___x_2188_, 2);
v_auxDeclNGen_2194_ = lean_ctor_get(v___x_2188_, 3);
v_traceState_2195_ = lean_ctor_get(v___x_2188_, 4);
v_messages_2196_ = lean_ctor_get(v___x_2188_, 6);
v_infoState_2197_ = lean_ctor_get(v___x_2188_, 7);
v_snapshotTasks_2198_ = lean_ctor_get(v___x_2188_, 8);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v___x_2188_, 5);
lean_dec(v_unused_2227_);
v___x_2200_ = v___x_2188_;
v_isShared_2201_ = v_isSharedCheck_2226_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_snapshotTasks_2198_);
lean_inc(v_infoState_2197_);
lean_inc(v_messages_2196_);
lean_inc(v_traceState_2195_);
lean_inc(v_auxDeclNGen_2194_);
lean_inc(v_ngen_2193_);
lean_inc(v_nextMacroScope_2192_);
lean_inc(v_env_2191_);
lean_dec(v___x_2188_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2226_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_asyncMode_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v_asyncMode_2202_ = lean_ctor_get(v_toEnvExtension_2190_, 2);
lean_inc(v_asyncMode_2202_);
lean_inc(v_decl_2179_);
v___x_2203_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2189_, v_env_2191_, v_decl_2179_, v_asyncMode_2202_, v_decl_2179_);
lean_dec(v_asyncMode_2202_);
v___x_2204_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 5, v___x_2204_);
lean_ctor_set(v___x_2200_, 0, v___x_2203_);
v___x_2206_ = v___x_2200_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_nextMacroScope_2192_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_ngen_2193_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_auxDeclNGen_2194_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_traceState_2195_);
lean_ctor_set(v_reuseFailAlloc_2225_, 5, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 6, v_messages_2196_);
lean_ctor_set(v_reuseFailAlloc_2225_, 7, v_infoState_2197_);
lean_ctor_set(v_reuseFailAlloc_2225_, 8, v_snapshotTasks_2198_);
v___x_2206_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_mctx_2209_; lean_object* v_zetaDeltaFVarIds_2210_; lean_object* v_postponed_2211_; lean_object* v_diag_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2223_; 
v___x_2207_ = lean_st_ref_set(v___y_2187_, v___x_2206_);
v___x_2208_ = lean_st_ref_take(v___y_2186_);
v_mctx_2209_ = lean_ctor_get(v___x_2208_, 0);
v_zetaDeltaFVarIds_2210_ = lean_ctor_get(v___x_2208_, 2);
v_postponed_2211_ = lean_ctor_get(v___x_2208_, 3);
v_diag_2212_ = lean_ctor_get(v___x_2208_, 4);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v___x_2208_, 1);
lean_dec(v_unused_2224_);
v___x_2214_ = v___x_2208_;
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_diag_2212_);
lean_inc(v_postponed_2211_);
lean_inc(v_zetaDeltaFVarIds_2210_);
lean_inc(v_mctx_2209_);
lean_dec(v___x_2208_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2216_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_mctx_2209_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_zetaDeltaFVarIds_2210_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_postponed_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_diag_2212_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_st_ref_set(v___y_2186_, v___x_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
}
}
v___jp_2230_:
{
lean_object* v_ext_2235_; lean_object* v_toEnvExtension_2236_; lean_object* v_attr_2237_; lean_object* v_asyncMode_2238_; uint8_t v___x_2239_; 
v_ext_2235_ = lean_ctor_get(v_attr_2178_, 1);
v_toEnvExtension_2236_ = lean_ctor_get(v_ext_2235_, 0);
v_attr_2237_ = lean_ctor_get(v_attr_2178_, 0);
v_asyncMode_2238_ = lean_ctor_get(v_toEnvExtension_2236_, 2);
lean_inc(v_decl_2179_);
lean_inc_ref(v_env_2229_);
v___x_2239_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2229_, v_decl_2179_, v_asyncMode_2238_);
if (v___x_2239_ == 0)
{
lean_object* v_toAttributeImplCore_2240_; lean_object* v_name_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_inc_ref(v_attr_2237_);
lean_dec_ref(v_attr_2178_);
v_toAttributeImplCore_2240_ = lean_ctor_get(v_attr_2237_, 0);
lean_inc_ref(v_toAttributeImplCore_2240_);
lean_dec_ref(v_attr_2237_);
v_name_2241_ = lean_ctor_get(v_toAttributeImplCore_2240_, 1);
lean_inc(v_name_2241_);
lean_dec_ref(v_toAttributeImplCore_2240_);
v___x_2242_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2229_);
v___x_2243_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2241_, v_decl_2179_, v___x_2242_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2243_;
}
else
{
lean_dec_ref(v_env_2229_);
v___y_2186_ = v___y_2232_;
v___y_2187_ = v___y_2234_;
goto v___jp_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2249_, lean_object* v_decl_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2249_, v_decl_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v_env_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2263_ = lean_st_ref_get(v___y_2261_);
v_env_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_env_2264_);
lean_dec(v___x_2263_);
v___x_2265_ = 0;
lean_inc(v_constName_2257_);
v___x_2266_ = l_Lean_Environment_find_x3f(v_env_2264_, v_constName_2257_, v___x_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2267_;
}
else
{
lean_object* v_val_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_constName_2257_);
v_val_2268_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2266_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_val_2268_);
lean_dec(v___x_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set_tag(v___x_2270_, 0);
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_val_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2286_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2287_ = lean_unsigned_to_nat(58u);
v___x_2288_ = lean_unsigned_to_nat(33u);
v___x_2289_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2290_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2291_ = l_mkPanicMessageWithDecl(v___x_2290_, v___x_2289_, v___x_2288_, v___x_2287_, v___x_2286_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2293_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2294_ = lean_unsigned_to_nat(60u);
v___x_2295_ = lean_unsigned_to_nat(30u);
v___x_2296_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2297_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2298_ = l_mkPanicMessageWithDecl(v___x_2297_, v___x_2296_, v___x_2295_, v___x_2294_, v___x_2293_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2299_, lean_object* v_indName_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; 
lean_inc(v_indName_2300_);
v___x_2306_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
if (lean_obj_tag(v_a_2307_) == 5)
{
lean_object* v_val_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2494_; 
v_val_2308_ = lean_ctor_get(v_a_2307_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2307_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2310_ = v_a_2307_;
v_isShared_2311_ = v_isSharedCheck_2494_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_val_2308_);
lean_dec(v_a_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2494_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_inc(v_indName_2300_);
v___x_2312_ = l_Lean_mkCasesOnName(v_indName_2300_);
lean_inc(v___x_2312_);
v___x_2313_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2312_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v_name_2315_; lean_object* v_levelParams_2316_; lean_object* v_type_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
v_name_2315_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_name_2315_);
v_levelParams_2316_ = lean_ctor_get(v_a_2314_, 1);
lean_inc_n(v_levelParams_2316_, 2);
v_type_2317_ = lean_ctor_get(v_a_2314_, 2);
lean_inc_ref(v_type_2317_);
lean_dec(v_a_2314_);
v___x_2318_ = lean_box(0);
v___x_2319_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2316_, v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 1)
{
lean_object* v_head_2320_; lean_object* v_tail_2321_; lean_object* v_numParams_2322_; lean_object* v_numIndices_2323_; lean_object* v_ctors_2324_; lean_object* v___f_2325_; lean_object* v___x_2327_; 
v_head_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_head_2320_);
v_tail_2321_ = lean_ctor_get(v___x_2319_, 1);
lean_inc(v_tail_2321_);
v_numParams_2322_ = lean_ctor_get(v_val_2308_, 1);
lean_inc_n(v_numParams_2322_, 2);
v_numIndices_2323_ = lean_ctor_get(v_val_2308_, 2);
lean_inc(v_numIndices_2323_);
v_ctors_2324_ = lean_ctor_get(v_val_2308_, 4);
lean_inc(v_ctors_2324_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2325_, 0, v_numIndices_2323_);
lean_closure_set(v___f_2325_, 1, v_head_2320_);
lean_closure_set(v___f_2325_, 2, v_ctors_2324_);
lean_closure_set(v___f_2325_, 3, v_tail_2321_);
lean_closure_set(v___f_2325_, 4, v_numParams_2322_);
lean_closure_set(v___f_2325_, 5, v_indName_2300_);
lean_closure_set(v___f_2325_, 6, v_val_2308_);
lean_closure_set(v___f_2325_, 7, v___x_2319_);
lean_closure_set(v___f_2325_, 8, v___x_2312_);
lean_closure_set(v___f_2325_, 9, v_name_2315_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 1);
lean_ctor_set(v___x_2310_, 0, v_numParams_2322_);
v___x_2327_ = v___x_2310_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_numParams_2322_);
v___x_2327_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
uint8_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = 0;
v___x_2329_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2317_, v___x_2327_, v___f_2325_, v___x_2328_, v___x_2328_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; uint8_t v___y_2334_; uint8_t v___x_2473_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = lean_box(v___x_2328_);
lean_inc(v_declName_2299_);
v___f_2332_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2332_, 0, v_a_2330_);
lean_closure_set(v___f_2332_, 1, v_declName_2299_);
lean_closure_set(v___f_2332_, 2, v_levelParams_2316_);
lean_closure_set(v___f_2332_, 3, v___x_2331_);
v___x_2473_ = l_Lean_isPrivateName(v_declName_2299_);
if (v___x_2473_ == 0)
{
uint8_t v___x_2474_; 
v___x_2474_ = 1;
v___y_2334_ = v___x_2474_;
goto v___jp_2333_;
}
else
{
v___y_2334_ = v___x_2328_;
goto v___jp_2333_;
}
v___jp_2333_:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2332_, v___y_2334_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v___x_2336_; lean_object* v_env_2337_; lean_object* v_nextMacroScope_2338_; lean_object* v_ngen_2339_; lean_object* v_auxDeclNGen_2340_; lean_object* v_traceState_2341_; lean_object* v_messages_2342_; lean_object* v_infoState_2343_; lean_object* v_snapshotTasks_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v___x_2335_);
v___x_2336_ = lean_st_ref_take(v_a_2304_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
v_nextMacroScope_2338_ = lean_ctor_get(v___x_2336_, 1);
v_ngen_2339_ = lean_ctor_get(v___x_2336_, 2);
v_auxDeclNGen_2340_ = lean_ctor_get(v___x_2336_, 3);
v_traceState_2341_ = lean_ctor_get(v___x_2336_, 4);
v_messages_2342_ = lean_ctor_get(v___x_2336_, 6);
v_infoState_2343_ = lean_ctor_get(v___x_2336_, 7);
v_snapshotTasks_2344_ = lean_ctor_get(v___x_2336_, 8);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v___x_2336_, 5);
lean_dec(v_unused_2472_);
v___x_2346_ = v___x_2336_;
v_isShared_2347_ = v_isSharedCheck_2471_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_snapshotTasks_2344_);
lean_inc(v_infoState_2343_);
lean_inc(v_messages_2342_);
lean_inc(v_traceState_2341_);
lean_inc(v_auxDeclNGen_2340_);
lean_inc(v_ngen_2339_);
lean_inc(v_nextMacroScope_2338_);
lean_inc(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2471_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_inc(v_declName_2299_);
v___x_2348_ = l_Lean_Meta_markMatcherLike(v_env_2337_, v_declName_2299_);
v___x_2349_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 5, v___x_2349_);
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2351_ = v___x_2346_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_nextMacroScope_2338_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_ngen_2339_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_auxDeclNGen_2340_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_traceState_2341_);
lean_ctor_set(v_reuseFailAlloc_2470_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2470_, 6, v_messages_2342_);
lean_ctor_set(v_reuseFailAlloc_2470_, 7, v_infoState_2343_);
lean_ctor_set(v_reuseFailAlloc_2470_, 8, v_snapshotTasks_2344_);
v___x_2351_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_mctx_2354_; lean_object* v_zetaDeltaFVarIds_2355_; lean_object* v_postponed_2356_; lean_object* v_diag_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2468_; 
v___x_2352_ = lean_st_ref_set(v_a_2304_, v___x_2351_);
v___x_2353_ = lean_st_ref_take(v_a_2302_);
v_mctx_2354_ = lean_ctor_get(v___x_2353_, 0);
v_zetaDeltaFVarIds_2355_ = lean_ctor_get(v___x_2353_, 2);
v_postponed_2356_ = lean_ctor_get(v___x_2353_, 3);
v_diag_2357_ = lean_ctor_get(v___x_2353_, 4);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2353_, 1);
lean_dec(v_unused_2469_);
v___x_2359_ = v___x_2353_;
v_isShared_2360_ = v_isSharedCheck_2468_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_diag_2357_);
lean_inc(v_postponed_2356_);
lean_inc(v_zetaDeltaFVarIds_2355_);
lean_inc(v_mctx_2354_);
lean_dec(v___x_2353_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2468_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___x_2361_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_mctx_2354_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_zetaDeltaFVarIds_2355_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_postponed_2356_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_diag_2357_);
v___x_2363_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_env_2366_; lean_object* v_nextMacroScope_2367_; lean_object* v_ngen_2368_; lean_object* v_auxDeclNGen_2369_; lean_object* v_traceState_2370_; lean_object* v_messages_2371_; lean_object* v_infoState_2372_; lean_object* v_snapshotTasks_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2465_; 
v___x_2364_ = lean_st_ref_set(v_a_2302_, v___x_2363_);
v___x_2365_ = lean_st_ref_take(v_a_2304_);
v_env_2366_ = lean_ctor_get(v___x_2365_, 0);
v_nextMacroScope_2367_ = lean_ctor_get(v___x_2365_, 1);
v_ngen_2368_ = lean_ctor_get(v___x_2365_, 2);
v_auxDeclNGen_2369_ = lean_ctor_get(v___x_2365_, 3);
v_traceState_2370_ = lean_ctor_get(v___x_2365_, 4);
v_messages_2371_ = lean_ctor_get(v___x_2365_, 6);
v_infoState_2372_ = lean_ctor_get(v___x_2365_, 7);
v_snapshotTasks_2373_ = lean_ctor_get(v___x_2365_, 8);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2365_, 5);
lean_dec(v_unused_2466_);
v___x_2375_ = v___x_2365_;
v_isShared_2376_ = v_isSharedCheck_2465_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_snapshotTasks_2373_);
lean_inc(v_infoState_2372_);
lean_inc(v_messages_2371_);
lean_inc(v_traceState_2370_);
lean_inc(v_auxDeclNGen_2369_);
lean_inc(v_ngen_2368_);
lean_inc(v_nextMacroScope_2367_);
lean_inc(v_env_2366_);
lean_dec(v___x_2365_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2465_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_inc(v_declName_2299_);
v___x_2377_ = l_Lean_markAuxRecursor(v_env_2366_, v_declName_2299_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 5, v___x_2349_);
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_nextMacroScope_2367_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v_ngen_2368_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v_auxDeclNGen_2369_);
lean_ctor_set(v_reuseFailAlloc_2464_, 4, v_traceState_2370_);
lean_ctor_set(v_reuseFailAlloc_2464_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2464_, 6, v_messages_2371_);
lean_ctor_set(v_reuseFailAlloc_2464_, 7, v_infoState_2372_);
lean_ctor_set(v_reuseFailAlloc_2464_, 8, v_snapshotTasks_2373_);
v___x_2379_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_mctx_2382_; lean_object* v_zetaDeltaFVarIds_2383_; lean_object* v_postponed_2384_; lean_object* v_diag_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2462_; 
v___x_2380_ = lean_st_ref_set(v_a_2304_, v___x_2379_);
v___x_2381_ = lean_st_ref_take(v_a_2302_);
v_mctx_2382_ = lean_ctor_get(v___x_2381_, 0);
v_zetaDeltaFVarIds_2383_ = lean_ctor_get(v___x_2381_, 2);
v_postponed_2384_ = lean_ctor_get(v___x_2381_, 3);
v_diag_2385_ = lean_ctor_get(v___x_2381_, 4);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2381_, 1);
lean_dec(v_unused_2463_);
v___x_2387_ = v___x_2381_;
v_isShared_2388_ = v_isSharedCheck_2462_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_diag_2385_);
lean_inc(v_postponed_2384_);
lean_inc(v_zetaDeltaFVarIds_2383_);
lean_inc(v_mctx_2382_);
lean_dec(v___x_2381_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2462_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2361_);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_mctx_2382_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_zetaDeltaFVarIds_2383_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_postponed_2384_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_diag_2385_);
v___x_2390_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_env_2393_; lean_object* v_nextMacroScope_2394_; lean_object* v_ngen_2395_; lean_object* v_auxDeclNGen_2396_; lean_object* v_traceState_2397_; lean_object* v_messages_2398_; lean_object* v_infoState_2399_; lean_object* v_snapshotTasks_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2459_; 
v___x_2391_ = lean_st_ref_set(v_a_2302_, v___x_2390_);
v___x_2392_ = lean_st_ref_take(v_a_2304_);
v_env_2393_ = lean_ctor_get(v___x_2392_, 0);
v_nextMacroScope_2394_ = lean_ctor_get(v___x_2392_, 1);
v_ngen_2395_ = lean_ctor_get(v___x_2392_, 2);
v_auxDeclNGen_2396_ = lean_ctor_get(v___x_2392_, 3);
v_traceState_2397_ = lean_ctor_get(v___x_2392_, 4);
v_messages_2398_ = lean_ctor_get(v___x_2392_, 6);
v_infoState_2399_ = lean_ctor_get(v___x_2392_, 7);
v_snapshotTasks_2400_ = lean_ctor_get(v___x_2392_, 8);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2392_, 5);
lean_dec(v_unused_2460_);
v___x_2402_ = v___x_2392_;
v_isShared_2403_ = v_isSharedCheck_2459_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snapshotTasks_2400_);
lean_inc(v_infoState_2399_);
lean_inc(v_messages_2398_);
lean_inc(v_traceState_2397_);
lean_inc(v_auxDeclNGen_2396_);
lean_inc(v_ngen_2395_);
lean_inc(v_nextMacroScope_2394_);
lean_inc(v_env_2393_);
lean_dec(v___x_2392_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2459_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_inc(v_declName_2299_);
v___x_2404_ = l_Lean_Meta_addToCompletionBlackList(v_env_2393_, v_declName_2299_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 5, v___x_2349_);
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_nextMacroScope_2394_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_ngen_2395_);
lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_auxDeclNGen_2396_);
lean_ctor_set(v_reuseFailAlloc_2458_, 4, v_traceState_2397_);
lean_ctor_set(v_reuseFailAlloc_2458_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2458_, 6, v_messages_2398_);
lean_ctor_set(v_reuseFailAlloc_2458_, 7, v_infoState_2399_);
lean_ctor_set(v_reuseFailAlloc_2458_, 8, v_snapshotTasks_2400_);
v___x_2406_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v_mctx_2409_; lean_object* v_zetaDeltaFVarIds_2410_; lean_object* v_postponed_2411_; lean_object* v_diag_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2456_; 
v___x_2407_ = lean_st_ref_set(v_a_2304_, v___x_2406_);
v___x_2408_ = lean_st_ref_take(v_a_2302_);
v_mctx_2409_ = lean_ctor_get(v___x_2408_, 0);
v_zetaDeltaFVarIds_2410_ = lean_ctor_get(v___x_2408_, 2);
v_postponed_2411_ = lean_ctor_get(v___x_2408_, 3);
v_diag_2412_ = lean_ctor_get(v___x_2408_, 4);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v___x_2408_, 1);
lean_dec(v_unused_2457_);
v___x_2414_ = v___x_2408_;
v_isShared_2415_ = v_isSharedCheck_2456_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_diag_2412_);
lean_inc(v_postponed_2411_);
lean_inc(v_zetaDeltaFVarIds_2410_);
lean_inc(v_mctx_2409_);
lean_dec(v___x_2408_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2456_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v___x_2361_);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_mctx_2409_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_zetaDeltaFVarIds_2410_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_postponed_2411_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_diag_2412_);
v___x_2417_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_env_2420_; lean_object* v_nextMacroScope_2421_; lean_object* v_ngen_2422_; lean_object* v_auxDeclNGen_2423_; lean_object* v_traceState_2424_; lean_object* v_messages_2425_; lean_object* v_infoState_2426_; lean_object* v_snapshotTasks_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2453_; 
v___x_2418_ = lean_st_ref_set(v_a_2302_, v___x_2417_);
v___x_2419_ = lean_st_ref_take(v_a_2304_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
v_nextMacroScope_2421_ = lean_ctor_get(v___x_2419_, 1);
v_ngen_2422_ = lean_ctor_get(v___x_2419_, 2);
v_auxDeclNGen_2423_ = lean_ctor_get(v___x_2419_, 3);
v_traceState_2424_ = lean_ctor_get(v___x_2419_, 4);
v_messages_2425_ = lean_ctor_get(v___x_2419_, 6);
v_infoState_2426_ = lean_ctor_get(v___x_2419_, 7);
v_snapshotTasks_2427_ = lean_ctor_get(v___x_2419_, 8);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2419_, 5);
lean_dec(v_unused_2454_);
v___x_2429_ = v___x_2419_;
v_isShared_2430_ = v_isSharedCheck_2453_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snapshotTasks_2427_);
lean_inc(v_infoState_2426_);
lean_inc(v_messages_2425_);
lean_inc(v_traceState_2424_);
lean_inc(v_auxDeclNGen_2423_);
lean_inc(v_ngen_2422_);
lean_inc(v_nextMacroScope_2421_);
lean_inc(v_env_2420_);
lean_dec(v___x_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2453_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_inc(v_declName_2299_);
v___x_2431_ = l_Lean_addProtected(v_env_2420_, v_declName_2299_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 5, v___x_2349_);
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_nextMacroScope_2421_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_ngen_2422_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_auxDeclNGen_2423_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_traceState_2424_);
lean_ctor_set(v_reuseFailAlloc_2452_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2452_, 6, v_messages_2425_);
lean_ctor_set(v_reuseFailAlloc_2452_, 7, v_infoState_2426_);
lean_ctor_set(v_reuseFailAlloc_2452_, 8, v_snapshotTasks_2427_);
v___x_2433_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_mctx_2436_; lean_object* v_zetaDeltaFVarIds_2437_; lean_object* v_postponed_2438_; lean_object* v_diag_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2450_; 
v___x_2434_ = lean_st_ref_set(v_a_2304_, v___x_2433_);
v___x_2435_ = lean_st_ref_take(v_a_2302_);
v_mctx_2436_ = lean_ctor_get(v___x_2435_, 0);
v_zetaDeltaFVarIds_2437_ = lean_ctor_get(v___x_2435_, 2);
v_postponed_2438_ = lean_ctor_get(v___x_2435_, 3);
v_diag_2439_ = lean_ctor_get(v___x_2435_, 4);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2435_, 1);
lean_dec(v_unused_2451_);
v___x_2441_ = v___x_2435_;
v_isShared_2442_ = v_isSharedCheck_2450_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_diag_2439_);
lean_inc(v_postponed_2438_);
lean_inc(v_zetaDeltaFVarIds_2437_);
lean_inc(v_mctx_2436_);
lean_dec(v___x_2435_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2450_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2361_);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_mctx_2436_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_zetaDeltaFVarIds_2437_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_postponed_2438_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_diag_2439_);
v___x_2444_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_st_ref_set(v_a_2302_, v___x_2444_);
v___x_2446_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2299_);
v___x_2447_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2446_, v_declName_2299_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v___x_2447_);
v___x_2448_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2299_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2448_;
}
else
{
lean_dec(v_declName_2299_);
return v___x_2447_;
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
lean_dec(v_declName_2299_);
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_levelParams_2316_);
lean_dec(v_declName_2299_);
v_a_2475_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2329_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2329_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v___x_2319_);
lean_dec_ref(v_type_2317_);
lean_dec(v_levelParams_2316_);
lean_dec(v_name_2315_);
lean_dec(v___x_2312_);
lean_del_object(v___x_2310_);
lean_dec_ref(v_val_2308_);
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v___x_2484_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2485_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2484_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2485_;
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v___x_2312_);
lean_del_object(v___x_2310_);
lean_dec_ref(v_val_2308_);
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v_a_2486_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2313_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2313_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v_a_2307_);
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v___x_2495_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2496_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2495_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2496_;
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v_a_2497_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2306_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2306_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2505_, lean_object* v_indName_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2505_, v_indName_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2513_, lean_object* v_name_2514_, lean_object* v_type_2515_, lean_object* v_k_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2514_, v_type_2515_, v_k_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2523_, lean_object* v_name_2524_, lean_object* v_type_2525_, lean_object* v_k_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2523_, v_name_2524_, v_type_2525_, v_k_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2533_, lean_object* v_params_2534_, lean_object* v_alts_2535_, lean_object* v___x_2536_, lean_object* v_ism2_2537_, lean_object* v_motive_2538_, lean_object* v_val_2539_, lean_object* v_indName_2540_, lean_object* v___x_2541_, lean_object* v___x_2542_, lean_object* v___x_2543_, lean_object* v_as_2544_, lean_object* v_i_2545_, lean_object* v_j_2546_, lean_object* v_inv_2547_, lean_object* v_bs_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2533_, v_params_2534_, v_alts_2535_, v___x_2536_, v_ism2_2537_, v_motive_2538_, v_val_2539_, v_indName_2540_, v___x_2541_, v___x_2542_, v___x_2543_, v_as_2544_, v_i_2545_, v_j_2546_, v_bs_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2555_ = _args[0];
lean_object* v_params_2556_ = _args[1];
lean_object* v_alts_2557_ = _args[2];
lean_object* v___x_2558_ = _args[3];
lean_object* v_ism2_2559_ = _args[4];
lean_object* v_motive_2560_ = _args[5];
lean_object* v_val_2561_ = _args[6];
lean_object* v_indName_2562_ = _args[7];
lean_object* v___x_2563_ = _args[8];
lean_object* v___x_2564_ = _args[9];
lean_object* v___x_2565_ = _args[10];
lean_object* v_as_2566_ = _args[11];
lean_object* v_i_2567_ = _args[12];
lean_object* v_j_2568_ = _args[13];
lean_object* v_inv_2569_ = _args[14];
lean_object* v_bs_2570_ = _args[15];
lean_object* v___y_2571_ = _args[16];
lean_object* v___y_2572_ = _args[17];
lean_object* v___y_2573_ = _args[18];
lean_object* v___y_2574_ = _args[19];
lean_object* v___y_2575_ = _args[20];
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2555_, v_params_2556_, v_alts_2557_, v___x_2558_, v_ism2_2559_, v_motive_2560_, v_val_2561_, v_indName_2562_, v___x_2563_, v___x_2564_, v___x_2565_, v_as_2566_, v_i_2567_, v_j_2568_, v_inv_2569_, v_bs_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_as_2566_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2577_, lean_object* v_params_2578_, lean_object* v___x_2579_, lean_object* v_motive_2580_, lean_object* v_as_2581_, lean_object* v_i_2582_, lean_object* v_j_2583_, lean_object* v_inv_2584_, lean_object* v_bs_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2577_, v_params_2578_, v___x_2579_, v_motive_2580_, v_as_2581_, v_i_2582_, v_j_2583_, v_bs_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2592_, lean_object* v_params_2593_, lean_object* v___x_2594_, lean_object* v_motive_2595_, lean_object* v_as_2596_, lean_object* v_i_2597_, lean_object* v_j_2598_, lean_object* v_inv_2599_, lean_object* v_bs_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2592_, v_params_2593_, v___x_2594_, v_motive_2595_, v_as_2596_, v_i_2597_, v_j_2598_, v_inv_2599_, v_bs_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_as_2596_);
lean_dec_ref(v_params_2593_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2607_, uint8_t v_s_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2607_, v_s_2608_, v___y_2610_, v___y_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2615_, lean_object* v_s_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v_s_boxed_2622_; lean_object* v_res_2623_; 
v_s_boxed_2622_ = lean_unbox(v_s_2616_);
v_res_2623_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2615_, v_s_boxed_2622_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2624_, lean_object* v_constName_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_constName_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2632_, v_constName_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2640_, lean_object* v_attrName_2641_, lean_object* v_declName_2642_, lean_object* v_asyncPrefix_x3f_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2641_, v_declName_2642_, v_asyncPrefix_x3f_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2650_, lean_object* v_attrName_2651_, lean_object* v_declName_2652_, lean_object* v_asyncPrefix_x3f_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2650_, v_attrName_2651_, v_declName_2652_, v_asyncPrefix_x3f_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2660_, lean_object* v_attrName_2661_, lean_object* v_declName_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2661_, v_declName_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_attrName_2670_, lean_object* v_declName_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2669_, v_attrName_2670_, v_declName_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2678_, lean_object* v_ref_2679_, lean_object* v_constName_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2679_, v_constName_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2687_, lean_object* v_ref_2688_, lean_object* v_constName_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2687_, v_ref_2688_, v_constName_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v_ref_2688_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2696_, lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2704_, v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2712_, lean_object* v_ref_2713_, lean_object* v_msg_2714_, lean_object* v_declHint_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2713_, v_msg_2714_, v_declHint_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_ref_2723_, lean_object* v_msg_2724_, lean_object* v_declHint_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2722_, v_ref_2723_, v_msg_2724_, v_declHint_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_ref_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2732_, lean_object* v_declHint_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2732_, v_declHint_2733_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2740_, lean_object* v_declHint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2740_, v_declHint_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2748_, lean_object* v_ref_2749_, lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2749_, v_msg_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2757_, lean_object* v_ref_2758_, lean_object* v_msg_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2757_, v_ref_2758_, v_msg_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_ref_2758_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Expr_hasMVar(v_e_2766_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_e_2766_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v_mctx_2772_; lean_object* v___x_2773_; lean_object* v_fst_2774_; lean_object* v_snd_2775_; lean_object* v___x_2776_; lean_object* v_cache_2777_; lean_object* v_zetaDeltaFVarIds_2778_; lean_object* v_postponed_2779_; lean_object* v_diag_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2789_; 
v___x_2771_ = lean_st_ref_get(v___y_2767_);
v_mctx_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_mctx_2772_);
lean_dec(v___x_2771_);
v___x_2773_ = l_Lean_instantiateMVarsCore(v_mctx_2772_, v_e_2766_);
v_fst_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_fst_2774_);
v_snd_2775_ = lean_ctor_get(v___x_2773_, 1);
lean_inc(v_snd_2775_);
lean_dec_ref(v___x_2773_);
v___x_2776_ = lean_st_ref_take(v___y_2767_);
v_cache_2777_ = lean_ctor_get(v___x_2776_, 1);
v_zetaDeltaFVarIds_2778_ = lean_ctor_get(v___x_2776_, 2);
v_postponed_2779_ = lean_ctor_get(v___x_2776_, 3);
v_diag_2780_ = lean_ctor_get(v___x_2776_, 4);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2776_, 0);
lean_dec(v_unused_2790_);
v___x_2782_ = v___x_2776_;
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_diag_2780_);
lean_inc(v_postponed_2779_);
lean_inc(v_zetaDeltaFVarIds_2778_);
lean_inc(v_cache_2777_);
lean_dec(v___x_2776_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v_snd_2775_);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_snd_2775_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_cache_2777_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_zetaDeltaFVarIds_2778_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_postponed_2779_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v_diag_2780_);
v___x_2785_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_st_ref_set(v___y_2767_, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_fst_2774_);
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2791_, v___y_2792_);
lean_dec(v___y_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2795_, v___y_2797_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2809_, lean_object* v_info_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; lean_object* v_nextMacroScope_2816_; lean_object* v_ngen_2817_; lean_object* v_auxDeclNGen_2818_; lean_object* v_traceState_2819_; lean_object* v_messages_2820_; lean_object* v_infoState_2821_; lean_object* v_snapshotTasks_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2849_; 
v___x_2814_ = lean_st_ref_take(v___y_2812_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
v_nextMacroScope_2816_ = lean_ctor_get(v___x_2814_, 1);
v_ngen_2817_ = lean_ctor_get(v___x_2814_, 2);
v_auxDeclNGen_2818_ = lean_ctor_get(v___x_2814_, 3);
v_traceState_2819_ = lean_ctor_get(v___x_2814_, 4);
v_messages_2820_ = lean_ctor_get(v___x_2814_, 6);
v_infoState_2821_ = lean_ctor_get(v___x_2814_, 7);
v_snapshotTasks_2822_ = lean_ctor_get(v___x_2814_, 8);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2814_, 5);
lean_dec(v_unused_2850_);
v___x_2824_ = v___x_2814_;
v_isShared_2825_ = v_isSharedCheck_2849_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_snapshotTasks_2822_);
lean_inc(v_infoState_2821_);
lean_inc(v_messages_2820_);
lean_inc(v_traceState_2819_);
lean_inc(v_auxDeclNGen_2818_);
lean_inc(v_ngen_2817_);
lean_inc(v_nextMacroScope_2816_);
lean_inc(v_env_2815_);
lean_dec(v___x_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2849_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2815_, v_matcherName_2809_, v_info_2810_);
v___x_2827_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 5, v___x_2827_);
lean_ctor_set(v___x_2824_, 0, v___x_2826_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_nextMacroScope_2816_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_ngen_2817_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_auxDeclNGen_2818_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_traceState_2819_);
lean_ctor_set(v_reuseFailAlloc_2848_, 5, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2848_, 6, v_messages_2820_);
lean_ctor_set(v_reuseFailAlloc_2848_, 7, v_infoState_2821_);
lean_ctor_set(v_reuseFailAlloc_2848_, 8, v_snapshotTasks_2822_);
v___x_2829_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_mctx_2832_; lean_object* v_zetaDeltaFVarIds_2833_; lean_object* v_postponed_2834_; lean_object* v_diag_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v___x_2830_ = lean_st_ref_set(v___y_2812_, v___x_2829_);
v___x_2831_ = lean_st_ref_take(v___y_2811_);
v_mctx_2832_ = lean_ctor_get(v___x_2831_, 0);
v_zetaDeltaFVarIds_2833_ = lean_ctor_get(v___x_2831_, 2);
v_postponed_2834_ = lean_ctor_get(v___x_2831_, 3);
v_diag_2835_ = lean_ctor_get(v___x_2831_, 4);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2831_, 1);
lean_dec(v_unused_2847_);
v___x_2837_ = v___x_2831_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_diag_2835_);
lean_inc(v_postponed_2834_);
lean_inc(v_zetaDeltaFVarIds_2833_);
lean_inc(v_mctx_2832_);
lean_dec(v___x_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v___x_2839_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_mctx_2832_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_zetaDeltaFVarIds_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_postponed_2834_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_diag_2835_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = lean_st_ref_set(v___y_2811_, v___x_2841_);
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2851_, lean_object* v_info_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2851_, v_info_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec(v___y_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2857_, lean_object* v_info_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2857_, v_info_2858_, v___y_2860_, v___y_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2865_, lean_object* v_info_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2865_, v_info_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2873_, lean_object* v___x_2874_, lean_object* v_newEqs1_2875_, uint8_t v___x_2876_, uint8_t v___x_2877_, uint8_t v___x_2878_, lean_object* v_ism1_x27_2879_, lean_object* v_ism2_x27_2880_, lean_object* v_newRefls1_2881_, lean_object* v_newEqs2_2882_, lean_object* v_newRefls2_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_mkAppN(v_motive_2873_, v___x_2874_);
v___x_2890_ = l_Array_append___redArg(v_newEqs1_2875_, v_newEqs2_2882_);
v___x_2891_ = l_Lean_Meta_mkForallFVars(v___x_2890_, v___x_2889_, v___x_2876_, v___x_2877_, v___x_2877_, v___x_2878_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec_ref(v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = l_Array_append___redArg(v_ism1_x27_2879_, v_ism2_x27_2880_);
v___x_2894_ = l_Lean_Meta_mkLambdaFVars(v___x_2893_, v_a_2892_, v___x_2876_, v___x_2877_, v___x_2876_, v___x_2877_, v___x_2878_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec_ref(v___x_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2904_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2899_ = l_Array_append___redArg(v_newRefls1_2881_, v_newRefls2_2883_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_a_2895_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2900_);
v___x_2902_ = v___x_2897_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v_newRefls1_2881_);
v_a_2905_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2894_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2894_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_newRefls1_2881_);
lean_dec_ref(v_ism1_x27_2879_);
v_a_2913_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2891_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2891_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2921_, lean_object* v___x_2922_, lean_object* v_newEqs1_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v_ism1_x27_2927_, lean_object* v_ism2_x27_2928_, lean_object* v_newRefls1_2929_, lean_object* v_newEqs2_2930_, lean_object* v_newRefls2_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v___x_15221__boxed_2937_; uint8_t v___x_15222__boxed_2938_; uint8_t v___x_15223__boxed_2939_; lean_object* v_res_2940_; 
v___x_15221__boxed_2937_ = lean_unbox(v___x_2924_);
v___x_15222__boxed_2938_ = lean_unbox(v___x_2925_);
v___x_15223__boxed_2939_ = lean_unbox(v___x_2926_);
v_res_2940_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2921_, v___x_2922_, v_newEqs1_2923_, v___x_15221__boxed_2937_, v___x_15222__boxed_2938_, v___x_15223__boxed_2939_, v_ism1_x27_2927_, v_ism2_x27_2928_, v_newRefls1_2929_, v_newEqs2_2930_, v_newRefls2_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v_newRefls2_2931_);
lean_dec_ref(v_newEqs2_2930_);
lean_dec_ref(v_ism2_x27_2928_);
lean_dec_ref(v___x_2922_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2941_, lean_object* v___x_2942_, uint8_t v___x_2943_, uint8_t v___x_2944_, uint8_t v___x_2945_, lean_object* v_ism1_x27_2946_, lean_object* v_ism2_x27_2947_, lean_object* v_is_2948_, lean_object* v___x_2949_, lean_object* v_newEqs1_2950_, lean_object* v_newRefls1_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2957_ = lean_box(v___x_2943_);
v___x_2958_ = lean_box(v___x_2944_);
v___x_2959_ = lean_box(v___x_2945_);
lean_inc_ref(v_ism2_x27_2947_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2960_, 0, v_motive_2941_);
lean_closure_set(v___f_2960_, 1, v___x_2942_);
lean_closure_set(v___f_2960_, 2, v_newEqs1_2950_);
lean_closure_set(v___f_2960_, 3, v___x_2957_);
lean_closure_set(v___f_2960_, 4, v___x_2958_);
lean_closure_set(v___f_2960_, 5, v___x_2959_);
lean_closure_set(v___f_2960_, 6, v_ism1_x27_2946_);
lean_closure_set(v___f_2960_, 7, v_ism2_x27_2947_);
lean_closure_set(v___f_2960_, 8, v_newRefls1_2951_);
v___x_2961_ = lean_array_push(v_is_2948_, v___x_2949_);
v___x_2962_ = l_Lean_Meta_withNewEqs___redArg(v___x_2961_, v_ism2_x27_2947_, v___f_2960_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v_ism1_x27_2968_, lean_object* v_ism2_x27_2969_, lean_object* v_is_2970_, lean_object* v___x_2971_, lean_object* v_newEqs1_2972_, lean_object* v_newRefls1_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v___x_15312__boxed_2979_; uint8_t v___x_15313__boxed_2980_; uint8_t v___x_15314__boxed_2981_; lean_object* v_res_2982_; 
v___x_15312__boxed_2979_ = lean_unbox(v___x_2965_);
v___x_15313__boxed_2980_ = lean_unbox(v___x_2966_);
v___x_15314__boxed_2981_ = lean_unbox(v___x_2967_);
v_res_2982_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2963_, v___x_2964_, v___x_15312__boxed_2979_, v___x_15313__boxed_2980_, v___x_15314__boxed_2981_, v_ism1_x27_2968_, v_ism2_x27_2969_, v_is_2970_, v___x_2971_, v_newEqs1_2972_, v_newRefls1_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2983_, uint8_t v___x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_addDecl(v___x_2983_, v___x_2984_, v___y_2987_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_2991_, lean_object* v___x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v___x_15354__boxed_2998_; lean_object* v_res_2999_; 
v___x_15354__boxed_2998_ = lean_unbox(v___x_2992_);
v_res_2999_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_2991_, v___x_15354__boxed_2998_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2999_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3002_ = l_Lean_stringToMessageData(v___x_3001_);
return v___x_3002_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3005_ = l_Lean_stringToMessageData(v___x_3004_);
return v___x_3005_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3013_ = l_Lean_mkConst(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3016_ = l_Lean_stringToMessageData(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3017_, lean_object* v_a_3018_, lean_object* v_j_3019_, lean_object* v_zs1_3020_, lean_object* v_snd_3021_, uint8_t v___x_3022_, uint8_t v_isZero_3023_, uint8_t v___x_3024_, lean_object* v_alts_3025_, lean_object* v_zs2_3026_, lean_object* v___ctorRet2_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_array_get_borrowed(v___x_3017_, v_a_3018_, v_j_3019_);
lean_inc_ref(v_zs1_3020_);
v___x_3034_ = l_Array_append___redArg(v_zs1_3020_, v_zs2_3026_);
lean_inc(v___x_3033_);
v___x_3035_ = l_Lean_Meta_instantiateForall(v___x_3033_, v___x_3034_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref(v___x_3035_);
v___x_3037_ = lean_box(0);
v___x_3038_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3036_, v___x_3037_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref(v___x_3038_);
v___x_3040_ = l_Lean_Expr_mvarId_x21(v_a_3039_);
v___x_3041_ = lean_array_get_size(v_snd_3021_);
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_box(0);
lean_inc_ref(v___y_3030_);
v___x_3044_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3041_, v___x_3040_, v___x_3042_, v___x_3043_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3044_);
if (lean_obj_tag(v_a_3045_) == 1)
{
lean_object* v_val_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3093_; 
v_val_3046_ = lean_ctor_get(v_a_3045_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_a_3045_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3048_ = v_a_3045_;
v_isShared_3049_ = v_isSharedCheck_3093_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_val_3046_);
lean_dec(v_a_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3093_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v_fst_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3091_; 
v_fst_3050_ = lean_ctor_get(v_val_3046_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_val_3046_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_val_3046_, 1);
lean_dec(v_unused_3092_);
v___x_3052_ = v_val_3046_;
v_isShared_3053_ = v_isSharedCheck_3091_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_fst_3050_);
lean_dec(v_val_3046_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3091_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___y_3055_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3083_ = lean_array_get_borrowed(v___x_3017_, v_alts_3025_, v_j_3019_);
v___x_3084_ = lean_array_get_size(v_zs1_3020_);
lean_dec_ref(v_zs1_3020_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_nat_dec_eq(v___x_3084_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_inc(v___x_3083_);
v___y_3055_ = v___x_3083_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = lean_array_get_size(v_zs2_3026_);
v___x_3088_ = lean_nat_dec_eq(v___x_3087_, v___x_3085_);
if (v___x_3088_ == 0)
{
lean_inc(v___x_3083_);
v___y_3055_ = v___x_3083_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3083_);
v___x_3090_ = l_Lean_Expr_app___override(v___x_3083_, v___x_3089_);
v___y_3055_ = v___x_3090_;
goto v___jp_3054_;
}
}
v___jp_3054_:
{
uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = 0;
v___x_3057_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3057_, 0, v___x_3056_);
lean_ctor_set_uint8(v___x_3057_, 1, v___x_3022_);
lean_ctor_set_uint8(v___x_3057_, 2, v_isZero_3023_);
lean_ctor_set_uint8(v___x_3057_, 3, v___x_3022_);
lean_inc_ref(v___y_3055_);
lean_inc(v_fst_3050_);
v___x_3058_ = l_Lean_MVarId_apply(v_fst_3050_, v___y_3055_, v___x_3057_, v___x_3043_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
if (lean_obj_tag(v_a_3059_) == 0)
{
lean_object* v___x_3060_; lean_object* v_a_3061_; lean_object* v___x_3062_; 
lean_dec_ref(v___y_3055_);
lean_del_object(v___x_3052_);
lean_dec(v_fst_3050_);
lean_del_object(v___x_3048_);
v___x_3060_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3039_, v___y_3029_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref(v___x_3060_);
v___x_3062_ = l_Lean_Meta_mkLambdaFVars(v___x_3034_, v_a_3061_, v_isZero_3023_, v___x_3022_, v_isZero_3023_, v___x_3022_, v___x_3024_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec_ref(v___x_3034_);
return v___x_3062_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3066_; 
lean_dec(v_a_3059_);
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
v___x_3063_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3064_ = l_Lean_MessageData_ofExpr(v___y_3055_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 7);
lean_ctor_set(v___x_3052_, 1, v___x_3064_);
lean_ctor_set(v___x_3052_, 0, v___x_3063_);
v___x_3066_ = v___x_3052_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3067_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v_fst_3050_);
v___x_3070_ = v___x_3048_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_fst_3050_);
v___x_3070_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3068_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3071_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v___y_3055_);
lean_del_object(v___x_3052_);
lean_dec(v_fst_3050_);
lean_del_object(v___x_3048_);
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
v_a_3075_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3058_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3058_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
v___x_3094_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3095_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3094_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3095_;
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
v_a_3096_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3044_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3044_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
return v___x_3038_;
}
}
else
{
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3104_, lean_object* v_a_3105_, lean_object* v_j_3106_, lean_object* v_zs1_3107_, lean_object* v_snd_3108_, lean_object* v___x_3109_, lean_object* v_isZero_3110_, lean_object* v___x_3111_, lean_object* v_alts_3112_, lean_object* v_zs2_3113_, lean_object* v___ctorRet2_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v___x_15413__boxed_3120_; uint8_t v_isZero_boxed_3121_; uint8_t v___x_15414__boxed_3122_; lean_object* v_res_3123_; 
v___x_15413__boxed_3120_ = lean_unbox(v___x_3109_);
v_isZero_boxed_3121_ = lean_unbox(v_isZero_3110_);
v___x_15414__boxed_3122_ = lean_unbox(v___x_3111_);
v_res_3123_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3104_, v_a_3105_, v_j_3106_, v_zs1_3107_, v_snd_3108_, v___x_15413__boxed_3120_, v_isZero_boxed_3121_, v___x_15414__boxed_3122_, v_alts_3112_, v_zs2_3113_, v___ctorRet2_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___ctorRet2_3114_);
lean_dec_ref(v_zs2_3113_);
lean_dec_ref(v_alts_3112_);
lean_dec_ref(v_snd_3108_);
lean_dec(v_j_3106_);
lean_dec_ref(v_a_3105_);
lean_dec_ref(v___x_3104_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3124_, lean_object* v_a_3125_, lean_object* v_j_3126_, lean_object* v_snd_3127_, uint8_t v___x_3128_, uint8_t v_isZero_3129_, uint8_t v___x_3130_, lean_object* v_alts_3131_, lean_object* v_a_3132_, lean_object* v_zs1_3133_, lean_object* v___ctorRet1_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; 
v___x_3140_ = lean_box(v___x_3128_);
v___x_3141_ = lean_box(v_isZero_3129_);
v___x_3142_ = lean_box(v___x_3130_);
v___f_3143_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3143_, 0, v___x_3124_);
lean_closure_set(v___f_3143_, 1, v_a_3125_);
lean_closure_set(v___f_3143_, 2, v_j_3126_);
lean_closure_set(v___f_3143_, 3, v_zs1_3133_);
lean_closure_set(v___f_3143_, 4, v_snd_3127_);
lean_closure_set(v___f_3143_, 5, v___x_3140_);
lean_closure_set(v___f_3143_, 6, v___x_3141_);
lean_closure_set(v___f_3143_, 7, v___x_3142_);
lean_closure_set(v___f_3143_, 8, v_alts_3131_);
v___x_3144_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3132_, v___f_3143_, v_isZero_3129_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3145_, lean_object* v_a_3146_, lean_object* v_j_3147_, lean_object* v_snd_3148_, lean_object* v___x_3149_, lean_object* v_isZero_3150_, lean_object* v___x_3151_, lean_object* v_alts_3152_, lean_object* v_a_3153_, lean_object* v_zs1_3154_, lean_object* v___ctorRet1_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v___x_15606__boxed_3161_; uint8_t v_isZero_boxed_3162_; uint8_t v___x_15607__boxed_3163_; lean_object* v_res_3164_; 
v___x_15606__boxed_3161_ = lean_unbox(v___x_3149_);
v_isZero_boxed_3162_ = lean_unbox(v_isZero_3150_);
v___x_15607__boxed_3163_ = lean_unbox(v___x_3151_);
v_res_3164_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3145_, v_a_3146_, v_j_3147_, v_snd_3148_, v___x_15606__boxed_3161_, v_isZero_boxed_3162_, v___x_15607__boxed_3163_, v_alts_3152_, v_a_3153_, v_zs1_3154_, v___ctorRet1_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v___ctorRet1_3155_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3165_, lean_object* v_params_3166_, lean_object* v_a_3167_, lean_object* v_snd_3168_, lean_object* v_alts_3169_, lean_object* v_as_3170_, lean_object* v_i_3171_, lean_object* v_j_3172_, lean_object* v_bs_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_zero_3179_; uint8_t v_isZero_3180_; 
v_zero_3179_ = lean_unsigned_to_nat(0u);
v_isZero_3180_ = lean_nat_dec_eq(v_i_3171_, v_zero_3179_);
if (v_isZero_3180_ == 1)
{
lean_object* v___x_3181_; 
lean_dec(v_j_3172_);
lean_dec(v_i_3171_);
lean_dec_ref(v_alts_3169_);
lean_dec_ref(v_snd_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_tail_3165_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_bs_3173_);
return v___x_3181_;
}
else
{
lean_object* v_one_3182_; lean_object* v_n_3183_; lean_object* v___y_3185_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_one_3182_ = lean_unsigned_to_nat(1u);
v_n_3183_ = lean_nat_sub(v_i_3171_, v_one_3182_);
lean_dec(v_i_3171_);
v___x_3198_ = lean_array_fget_borrowed(v_as_3170_, v_j_3172_);
lean_inc(v_tail_3165_);
lean_inc(v___x_3198_);
v___x_3199_ = l_Lean_mkConst(v___x_3198_, v_tail_3165_);
v___x_3200_ = l_Lean_mkAppN(v___x_3199_, v_params_3166_);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
v___x_3201_ = lean_infer_type(v___x_3200_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc_n(v_a_3202_, 2);
lean_dec_ref(v___x_3201_);
v___x_3203_ = l_Lean_instInhabitedExpr;
v___x_3204_ = 1;
v___x_3205_ = 1;
v___x_3206_ = lean_box(v___x_3204_);
v___x_3207_ = lean_box(v_isZero_3180_);
v___x_3208_ = lean_box(v___x_3205_);
lean_inc_ref(v_alts_3169_);
lean_inc_ref(v_snd_3168_);
lean_inc(v_j_3172_);
lean_inc_ref(v_a_3167_);
v___f_3209_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3209_, 0, v___x_3203_);
lean_closure_set(v___f_3209_, 1, v_a_3167_);
lean_closure_set(v___f_3209_, 2, v_j_3172_);
lean_closure_set(v___f_3209_, 3, v_snd_3168_);
lean_closure_set(v___f_3209_, 4, v___x_3206_);
lean_closure_set(v___f_3209_, 5, v___x_3207_);
lean_closure_set(v___f_3209_, 6, v___x_3208_);
lean_closure_set(v___f_3209_, 7, v_alts_3169_);
lean_closure_set(v___f_3209_, 8, v_a_3202_);
v___x_3210_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3202_, v___f_3209_, v_isZero_3180_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
v___y_3185_ = v___x_3210_;
goto v___jp_3184_;
}
else
{
v___y_3185_ = v___x_3201_;
goto v___jp_3184_;
}
v___jp_3184_:
{
if (lean_obj_tag(v___y_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_a_3186_ = lean_ctor_get(v___y_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref(v___y_3185_);
v___x_3187_ = lean_nat_add(v_j_3172_, v_one_3182_);
lean_dec(v_j_3172_);
v___x_3188_ = lean_array_push(v_bs_3173_, v_a_3186_);
v_i_3171_ = v_n_3183_;
v_j_3172_ = v___x_3187_;
v_bs_3173_ = v___x_3188_;
goto _start;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_n_3183_);
lean_dec_ref(v_bs_3173_);
lean_dec(v_j_3172_);
lean_dec_ref(v_alts_3169_);
lean_dec_ref(v_snd_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_tail_3165_);
v_a_3190_ = lean_ctor_get(v___y_3185_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___y_3185_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___y_3185_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___y_3185_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3211_, lean_object* v_params_3212_, lean_object* v_a_3213_, lean_object* v_snd_3214_, lean_object* v_alts_3215_, lean_object* v_as_3216_, lean_object* v_i_3217_, lean_object* v_j_3218_, lean_object* v_bs_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3211_, v_params_3212_, v_a_3213_, v_snd_3214_, v_alts_3215_, v_as_3216_, v_i_3217_, v_j_3218_, v_bs_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v_as_3216_);
lean_dec_ref(v_params_3212_);
return v_res_3225_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_unsigned_to_nat(16u);
v___x_3228_ = lean_mk_array(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3229_, lean_object* v___x_3230_, uint8_t v___x_3231_, uint8_t v___x_3232_, uint8_t v___x_3233_, lean_object* v_ism1_x27_3234_, lean_object* v_is_3235_, lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v_params_3240_, lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v_heq_3243_, lean_object* v_val_3244_, lean_object* v___x_3245_, lean_object* v_tail_3246_, lean_object* v_alts_3247_, lean_object* v___x_3248_, lean_object* v___x_3249_, lean_object* v___x_3250_, lean_object* v_declName_3251_, lean_object* v_levelParams_3252_, lean_object* v_numIndices_3253_, lean_object* v___x_3254_, lean_object* v_numParams_3255_, lean_object* v_snd_3256_, lean_object* v_ism2_x27_3257_, lean_object* v_x_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___f_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3264_ = lean_box(v___x_3231_);
v___x_3265_ = lean_box(v___x_3232_);
v___x_3266_ = lean_box(v___x_3233_);
lean_inc_ref(v___x_3236_);
lean_inc_ref_n(v_is_3235_, 2);
lean_inc_ref(v_ism1_x27_3234_);
lean_inc_ref(v_motive_3229_);
v___f_3267_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3267_, 0, v_motive_3229_);
lean_closure_set(v___f_3267_, 1, v___x_3230_);
lean_closure_set(v___f_3267_, 2, v___x_3264_);
lean_closure_set(v___f_3267_, 3, v___x_3265_);
lean_closure_set(v___f_3267_, 4, v___x_3266_);
lean_closure_set(v___f_3267_, 5, v_ism1_x27_3234_);
lean_closure_set(v___f_3267_, 6, v_ism2_x27_3257_);
lean_closure_set(v___f_3267_, 7, v_is_3235_);
lean_closure_set(v___f_3267_, 8, v___x_3236_);
lean_inc_ref(v___x_3237_);
v___x_3268_ = lean_array_push(v_is_3235_, v___x_3237_);
v___x_3269_ = l_Lean_Meta_withNewEqs___redArg(v___x_3268_, v_ism1_x27_3234_, v___f_3267_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v_fst_3271_; lean_object* v_snd_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3374_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v_fst_3271_ = lean_ctor_get(v_a_3270_, 0);
v_snd_3272_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3274_ = v_a_3270_;
v_isShared_3275_ = v_isSharedCheck_3374_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_snd_3272_);
lean_inc(v_fst_3271_);
lean_dec(v_a_3270_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3374_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3276_ = l_Lean_mkConst(v___x_3238_, v___x_3239_);
v___x_3277_ = l_Lean_mkAppN(v___x_3276_, v_params_3240_);
v___x_3278_ = l_Lean_Expr_app___override(v___x_3277_, v_fst_3271_);
lean_inc_ref(v_is_3235_);
v___x_3279_ = l_Array_append___redArg(v_is_3235_, v___x_3241_);
v___x_3280_ = l_Array_append___redArg(v___x_3279_, v_is_3235_);
v___x_3281_ = l_Array_append___redArg(v___x_3280_, v___x_3242_);
v___x_3282_ = l_Lean_mkAppN(v___x_3278_, v___x_3281_);
lean_dec_ref(v___x_3281_);
lean_inc_ref(v_heq_3243_);
v___x_3283_ = l_Lean_Expr_app___override(v___x_3282_, v_heq_3243_);
v___x_3284_ = l_Lean_InductiveVal_numCtors(v_val_3244_);
lean_inc_ref(v___x_3283_);
v___x_3285_ = l_Lean_Meta_inferArgumentTypesN(v___x_3284_, v___x_3283_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = lean_mk_empty_array_with_capacity(v___x_3245_);
lean_inc(v___x_3249_);
lean_inc_ref(v_alts_3247_);
lean_inc(v_snd_3272_);
v___x_3288_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3246_, v_params_3240_, v_a_3286_, v_snd_3272_, v_alts_3247_, v___x_3248_, v___x_3245_, v___x_3249_, v___x_3287_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref(v___x_3288_);
v___x_3290_ = l_Lean_mkAppN(v___x_3283_, v_a_3289_);
lean_dec(v_a_3289_);
v___x_3291_ = l_Lean_mkAppN(v___x_3290_, v_snd_3272_);
lean_dec(v_snd_3272_);
lean_inc_ref(v___x_3250_);
v___x_3292_ = lean_array_push(v___x_3250_, v_motive_3229_);
v___x_3293_ = l_Array_append___redArg(v_params_3240_, v___x_3292_);
lean_dec_ref(v___x_3292_);
v___x_3294_ = l_Array_append___redArg(v___x_3293_, v_is_3235_);
lean_dec_ref(v_is_3235_);
v___x_3295_ = lean_unsigned_to_nat(2u);
v___x_3296_ = lean_mk_empty_array_with_capacity(v___x_3295_);
v___x_3297_ = lean_array_push(v___x_3296_, v___x_3237_);
v___x_3298_ = lean_array_push(v___x_3297_, v___x_3236_);
v___x_3299_ = l_Array_append___redArg(v___x_3294_, v___x_3298_);
lean_dec_ref(v___x_3298_);
v___x_3300_ = lean_array_push(v___x_3250_, v_heq_3243_);
v___x_3301_ = l_Array_append___redArg(v___x_3299_, v___x_3300_);
lean_dec_ref(v___x_3300_);
v___x_3302_ = l_Array_append___redArg(v___x_3301_, v_alts_3247_);
lean_dec_ref(v_alts_3247_);
v___x_3303_ = l_Lean_Meta_mkLambdaFVars(v___x_3302_, v___x_3291_, v___x_3231_, v___x_3232_, v___x_3231_, v___x_3232_, v___x_3233_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec_ref(v___x_3302_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc_n(v_a_3304_, 2);
lean_dec_ref(v___x_3303_);
lean_inc(v___y_3262_);
lean_inc_ref(v___y_3261_);
lean_inc(v___y_3260_);
lean_inc_ref(v___y_3259_);
v___x_3305_ = lean_infer_type(v_a_3304_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3341_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = lean_box(1);
lean_inc(v_declName_3251_);
v___x_3308_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3251_, v_levelParams_3252_, v_a_3306_, v_a_3304_, v___x_3307_, v___y_3262_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3341_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3341_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set_tag(v___x_3311_, 1);
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3315_; lean_object* v___f_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3315_ = lean_box(v___x_3231_);
lean_inc_ref(v___x_3314_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3316_, 0, v___x_3314_);
lean_closure_set(v___f_3316_, 1, v___x_3315_);
v___x_3317_ = lean_nat_add(v_numIndices_3253_, v___x_3254_);
lean_inc(v___x_3249_);
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3249_);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_mk_empty_array_with_capacity(v___x_3254_);
v___x_3321_ = lean_array_push(v___x_3320_, v___x_3319_);
v___x_3322_ = lean_array_push(v___x_3321_, v___x_3319_);
v___x_3323_ = lean_array_push(v___x_3322_, v___x_3319_);
v___x_3324_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 1, v___x_3324_);
lean_ctor_set(v___x_3274_, 0, v___x_3249_);
v___x_3326_ = v___x_3274_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; uint8_t v___y_3329_; uint8_t v___x_3338_; 
v___x_3327_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3327_, 0, v_numParams_3255_);
lean_ctor_set(v___x_3327_, 1, v___x_3317_);
lean_ctor_set(v___x_3327_, 2, v_snd_3256_);
lean_ctor_set(v___x_3327_, 3, v___x_3318_);
lean_ctor_set(v___x_3327_, 4, v___x_3323_);
lean_ctor_set(v___x_3327_, 5, v___x_3326_);
v___x_3338_ = l_Lean_isPrivateName(v_declName_3251_);
if (v___x_3338_ == 0)
{
v___y_3329_ = v___x_3232_;
goto v___jp_3328_;
}
else
{
v___y_3329_ = v___x_3231_;
goto v___jp_3328_;
}
v___jp_3328_:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3316_, v___y_3329_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec_ref(v___x_3330_);
v___x_3331_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3251_);
v___x_3332_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3331_, v_declName_3251_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v___x_3332_);
lean_inc_n(v_declName_3251_, 2);
v___x_3333_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3251_, v___x_3327_, v___y_3260_, v___y_3262_);
lean_dec_ref(v___x_3333_);
v___x_3334_ = 0;
v___x_3335_ = l_Lean_Meta_setInlineAttribute(v_declName_3251_, v___x_3334_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v___x_3336_; 
lean_dec_ref(v___x_3335_);
v___x_3336_ = l_Lean_enableRealizationsForConst(v_declName_3251_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v___x_3337_; 
lean_dec_ref(v___x_3336_);
v___x_3337_ = l_Lean_compileDecl(v___x_3314_, v___x_3232_, v___y_3261_, v___y_3262_);
return v___x_3337_;
}
else
{
lean_dec_ref(v___x_3314_);
return v___x_3336_;
}
}
else
{
lean_dec_ref(v___x_3314_);
lean_dec(v_declName_3251_);
return v___x_3335_;
}
}
else
{
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3314_);
lean_dec(v_declName_3251_);
return v___x_3332_;
}
}
else
{
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3314_);
lean_dec(v_declName_3251_);
return v___x_3330_;
}
}
}
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v_a_3304_);
lean_del_object(v___x_3274_);
lean_dec_ref(v_snd_3256_);
lean_dec(v_numParams_3255_);
lean_dec(v_levelParams_3252_);
lean_dec(v_declName_3251_);
lean_dec(v___x_3249_);
v_a_3342_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3305_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3305_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_del_object(v___x_3274_);
lean_dec_ref(v_snd_3256_);
lean_dec(v_numParams_3255_);
lean_dec(v_levelParams_3252_);
lean_dec(v_declName_3251_);
lean_dec(v___x_3249_);
v_a_3350_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3303_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3303_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v___x_3283_);
lean_del_object(v___x_3274_);
lean_dec(v_snd_3272_);
lean_dec_ref(v_snd_3256_);
lean_dec(v_numParams_3255_);
lean_dec(v_levelParams_3252_);
lean_dec(v_declName_3251_);
lean_dec_ref(v___x_3250_);
lean_dec(v___x_3249_);
lean_dec_ref(v_alts_3247_);
lean_dec_ref(v_heq_3243_);
lean_dec_ref(v_params_3240_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v___x_3236_);
lean_dec_ref(v_is_3235_);
lean_dec_ref(v_motive_3229_);
v_a_3358_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3288_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3288_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec_ref(v___x_3283_);
lean_del_object(v___x_3274_);
lean_dec(v_snd_3272_);
lean_dec_ref(v_snd_3256_);
lean_dec(v_numParams_3255_);
lean_dec(v_levelParams_3252_);
lean_dec(v_declName_3251_);
lean_dec_ref(v___x_3250_);
lean_dec(v___x_3249_);
lean_dec_ref(v_alts_3247_);
lean_dec(v_tail_3246_);
lean_dec(v___x_3245_);
lean_dec_ref(v_heq_3243_);
lean_dec_ref(v_params_3240_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v___x_3236_);
lean_dec_ref(v_is_3235_);
lean_dec_ref(v_motive_3229_);
v_a_3366_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3285_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3285_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v_snd_3256_);
lean_dec(v_numParams_3255_);
lean_dec(v_levelParams_3252_);
lean_dec(v_declName_3251_);
lean_dec_ref(v___x_3250_);
lean_dec(v___x_3249_);
lean_dec_ref(v_alts_3247_);
lean_dec(v_tail_3246_);
lean_dec(v___x_3245_);
lean_dec_ref(v_heq_3243_);
lean_dec_ref(v_params_3240_);
lean_dec(v___x_3239_);
lean_dec(v___x_3238_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v___x_3236_);
lean_dec_ref(v_is_3235_);
lean_dec_ref(v_motive_3229_);
v_a_3375_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3269_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3269_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3383_ = _args[0];
lean_object* v___x_3384_ = _args[1];
lean_object* v___x_3385_ = _args[2];
lean_object* v___x_3386_ = _args[3];
lean_object* v___x_3387_ = _args[4];
lean_object* v_ism1_x27_3388_ = _args[5];
lean_object* v_is_3389_ = _args[6];
lean_object* v___x_3390_ = _args[7];
lean_object* v___x_3391_ = _args[8];
lean_object* v___x_3392_ = _args[9];
lean_object* v___x_3393_ = _args[10];
lean_object* v_params_3394_ = _args[11];
lean_object* v___x_3395_ = _args[12];
lean_object* v___x_3396_ = _args[13];
lean_object* v_heq_3397_ = _args[14];
lean_object* v_val_3398_ = _args[15];
lean_object* v___x_3399_ = _args[16];
lean_object* v_tail_3400_ = _args[17];
lean_object* v_alts_3401_ = _args[18];
lean_object* v___x_3402_ = _args[19];
lean_object* v___x_3403_ = _args[20];
lean_object* v___x_3404_ = _args[21];
lean_object* v_declName_3405_ = _args[22];
lean_object* v_levelParams_3406_ = _args[23];
lean_object* v_numIndices_3407_ = _args[24];
lean_object* v___x_3408_ = _args[25];
lean_object* v_numParams_3409_ = _args[26];
lean_object* v_snd_3410_ = _args[27];
lean_object* v_ism2_x27_3411_ = _args[28];
lean_object* v_x_3412_ = _args[29];
lean_object* v___y_3413_ = _args[30];
lean_object* v___y_3414_ = _args[31];
lean_object* v___y_3415_ = _args[32];
lean_object* v___y_3416_ = _args[33];
lean_object* v___y_3417_ = _args[34];
_start:
{
uint8_t v___x_15736__boxed_3418_; uint8_t v___x_15737__boxed_3419_; uint8_t v___x_15738__boxed_3420_; lean_object* v_res_3421_; 
v___x_15736__boxed_3418_ = lean_unbox(v___x_3385_);
v___x_15737__boxed_3419_ = lean_unbox(v___x_3386_);
v___x_15738__boxed_3420_ = lean_unbox(v___x_3387_);
v_res_3421_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3383_, v___x_3384_, v___x_15736__boxed_3418_, v___x_15737__boxed_3419_, v___x_15738__boxed_3420_, v_ism1_x27_3388_, v_is_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v___x_3393_, v_params_3394_, v___x_3395_, v___x_3396_, v_heq_3397_, v_val_3398_, v___x_3399_, v_tail_3400_, v_alts_3401_, v___x_3402_, v___x_3403_, v___x_3404_, v_declName_3405_, v_levelParams_3406_, v_numIndices_3407_, v___x_3408_, v_numParams_3409_, v_snd_3410_, v_ism2_x27_3411_, v_x_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec_ref(v_x_3412_);
lean_dec(v___x_3408_);
lean_dec(v_numIndices_3407_);
lean_dec_ref(v___x_3402_);
lean_dec_ref(v_val_3398_);
lean_dec_ref(v___x_3396_);
lean_dec_ref(v___x_3395_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3422_, lean_object* v___x_3423_, uint8_t v___x_3424_, uint8_t v___x_3425_, uint8_t v___x_3426_, lean_object* v_is_3427_, lean_object* v___x_3428_, lean_object* v___x_3429_, lean_object* v___x_3430_, lean_object* v___x_3431_, lean_object* v_params_3432_, lean_object* v___x_3433_, lean_object* v___x_3434_, lean_object* v_heq_3435_, lean_object* v_val_3436_, lean_object* v___x_3437_, lean_object* v_tail_3438_, lean_object* v_alts_3439_, lean_object* v___x_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v_declName_3443_, lean_object* v_levelParams_3444_, lean_object* v_numIndices_3445_, lean_object* v___x_3446_, lean_object* v_numParams_3447_, lean_object* v_snd_3448_, lean_object* v___x_3449_, lean_object* v___x_3450_, lean_object* v_ism1_x27_3451_, lean_object* v_x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; 
v___x_3458_ = lean_box(v___x_3424_);
v___x_3459_ = lean_box(v___x_3425_);
v___x_3460_ = lean_box(v___x_3426_);
v___f_3461_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 35, 28);
lean_closure_set(v___f_3461_, 0, v_motive_3422_);
lean_closure_set(v___f_3461_, 1, v___x_3423_);
lean_closure_set(v___f_3461_, 2, v___x_3458_);
lean_closure_set(v___f_3461_, 3, v___x_3459_);
lean_closure_set(v___f_3461_, 4, v___x_3460_);
lean_closure_set(v___f_3461_, 5, v_ism1_x27_3451_);
lean_closure_set(v___f_3461_, 6, v_is_3427_);
lean_closure_set(v___f_3461_, 7, v___x_3428_);
lean_closure_set(v___f_3461_, 8, v___x_3429_);
lean_closure_set(v___f_3461_, 9, v___x_3430_);
lean_closure_set(v___f_3461_, 10, v___x_3431_);
lean_closure_set(v___f_3461_, 11, v_params_3432_);
lean_closure_set(v___f_3461_, 12, v___x_3433_);
lean_closure_set(v___f_3461_, 13, v___x_3434_);
lean_closure_set(v___f_3461_, 14, v_heq_3435_);
lean_closure_set(v___f_3461_, 15, v_val_3436_);
lean_closure_set(v___f_3461_, 16, v___x_3437_);
lean_closure_set(v___f_3461_, 17, v_tail_3438_);
lean_closure_set(v___f_3461_, 18, v_alts_3439_);
lean_closure_set(v___f_3461_, 19, v___x_3440_);
lean_closure_set(v___f_3461_, 20, v___x_3441_);
lean_closure_set(v___f_3461_, 21, v___x_3442_);
lean_closure_set(v___f_3461_, 22, v_declName_3443_);
lean_closure_set(v___f_3461_, 23, v_levelParams_3444_);
lean_closure_set(v___f_3461_, 24, v_numIndices_3445_);
lean_closure_set(v___f_3461_, 25, v___x_3446_);
lean_closure_set(v___f_3461_, 26, v_numParams_3447_);
lean_closure_set(v___f_3461_, 27, v_snd_3448_);
v___x_3462_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3449_, v___x_3450_, v___f_3461_, v___x_3424_, v___x_3424_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3463_ = _args[0];
lean_object* v___x_3464_ = _args[1];
lean_object* v___x_3465_ = _args[2];
lean_object* v___x_3466_ = _args[3];
lean_object* v___x_3467_ = _args[4];
lean_object* v_is_3468_ = _args[5];
lean_object* v___x_3469_ = _args[6];
lean_object* v___x_3470_ = _args[7];
lean_object* v___x_3471_ = _args[8];
lean_object* v___x_3472_ = _args[9];
lean_object* v_params_3473_ = _args[10];
lean_object* v___x_3474_ = _args[11];
lean_object* v___x_3475_ = _args[12];
lean_object* v_heq_3476_ = _args[13];
lean_object* v_val_3477_ = _args[14];
lean_object* v___x_3478_ = _args[15];
lean_object* v_tail_3479_ = _args[16];
lean_object* v_alts_3480_ = _args[17];
lean_object* v___x_3481_ = _args[18];
lean_object* v___x_3482_ = _args[19];
lean_object* v___x_3483_ = _args[20];
lean_object* v_declName_3484_ = _args[21];
lean_object* v_levelParams_3485_ = _args[22];
lean_object* v_numIndices_3486_ = _args[23];
lean_object* v___x_3487_ = _args[24];
lean_object* v_numParams_3488_ = _args[25];
lean_object* v_snd_3489_ = _args[26];
lean_object* v___x_3490_ = _args[27];
lean_object* v___x_3491_ = _args[28];
lean_object* v_ism1_x27_3492_ = _args[29];
lean_object* v_x_3493_ = _args[30];
lean_object* v___y_3494_ = _args[31];
lean_object* v___y_3495_ = _args[32];
lean_object* v___y_3496_ = _args[33];
lean_object* v___y_3497_ = _args[34];
lean_object* v___y_3498_ = _args[35];
_start:
{
uint8_t v___x_16060__boxed_3499_; uint8_t v___x_16061__boxed_3500_; uint8_t v___x_16062__boxed_3501_; lean_object* v_res_3502_; 
v___x_16060__boxed_3499_ = lean_unbox(v___x_3465_);
v___x_16061__boxed_3500_ = lean_unbox(v___x_3466_);
v___x_16062__boxed_3501_ = lean_unbox(v___x_3467_);
v_res_3502_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3463_, v___x_3464_, v___x_16060__boxed_3499_, v___x_16061__boxed_3500_, v___x_16062__boxed_3501_, v_is_3468_, v___x_3469_, v___x_3470_, v___x_3471_, v___x_3472_, v_params_3473_, v___x_3474_, v___x_3475_, v_heq_3476_, v_val_3477_, v___x_3478_, v_tail_3479_, v_alts_3480_, v___x_3481_, v___x_3482_, v___x_3483_, v_declName_3484_, v_levelParams_3485_, v_numIndices_3486_, v___x_3487_, v_numParams_3488_, v_snd_3489_, v___x_3490_, v___x_3491_, v_ism1_x27_3492_, v_x_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_x_3493_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3503_, lean_object* v___x_3504_, lean_object* v_motive_3505_, lean_object* v___x_3506_, uint8_t v___x_3507_, uint8_t v___x_3508_, uint8_t v___x_3509_, lean_object* v_is_3510_, lean_object* v___x_3511_, lean_object* v___x_3512_, lean_object* v___x_3513_, lean_object* v___x_3514_, lean_object* v_params_3515_, lean_object* v___x_3516_, lean_object* v___x_3517_, lean_object* v_heq_3518_, lean_object* v_val_3519_, lean_object* v___x_3520_, lean_object* v_tail_3521_, lean_object* v___x_3522_, lean_object* v___x_3523_, lean_object* v___x_3524_, lean_object* v_declName_3525_, lean_object* v_levelParams_3526_, lean_object* v___x_3527_, lean_object* v_numParams_3528_, lean_object* v_snd_3529_, lean_object* v___x_3530_, lean_object* v_alts_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___f_3542_; lean_object* v___x_3543_; 
v___x_3537_ = lean_nat_add(v_numIndices_3503_, v___x_3504_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
v___x_3539_ = lean_box(v___x_3507_);
v___x_3540_ = lean_box(v___x_3508_);
v___x_3541_ = lean_box(v___x_3509_);
lean_inc_ref(v___x_3538_);
lean_inc_ref(v___x_3530_);
v___f_3542_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 36, 29);
lean_closure_set(v___f_3542_, 0, v_motive_3505_);
lean_closure_set(v___f_3542_, 1, v___x_3506_);
lean_closure_set(v___f_3542_, 2, v___x_3539_);
lean_closure_set(v___f_3542_, 3, v___x_3540_);
lean_closure_set(v___f_3542_, 4, v___x_3541_);
lean_closure_set(v___f_3542_, 5, v_is_3510_);
lean_closure_set(v___f_3542_, 6, v___x_3511_);
lean_closure_set(v___f_3542_, 7, v___x_3512_);
lean_closure_set(v___f_3542_, 8, v___x_3513_);
lean_closure_set(v___f_3542_, 9, v___x_3514_);
lean_closure_set(v___f_3542_, 10, v_params_3515_);
lean_closure_set(v___f_3542_, 11, v___x_3516_);
lean_closure_set(v___f_3542_, 12, v___x_3517_);
lean_closure_set(v___f_3542_, 13, v_heq_3518_);
lean_closure_set(v___f_3542_, 14, v_val_3519_);
lean_closure_set(v___f_3542_, 15, v___x_3520_);
lean_closure_set(v___f_3542_, 16, v_tail_3521_);
lean_closure_set(v___f_3542_, 17, v_alts_3531_);
lean_closure_set(v___f_3542_, 18, v___x_3522_);
lean_closure_set(v___f_3542_, 19, v___x_3523_);
lean_closure_set(v___f_3542_, 20, v___x_3524_);
lean_closure_set(v___f_3542_, 21, v_declName_3525_);
lean_closure_set(v___f_3542_, 22, v_levelParams_3526_);
lean_closure_set(v___f_3542_, 23, v_numIndices_3503_);
lean_closure_set(v___f_3542_, 24, v___x_3527_);
lean_closure_set(v___f_3542_, 25, v_numParams_3528_);
lean_closure_set(v___f_3542_, 26, v_snd_3529_);
lean_closure_set(v___f_3542_, 27, v___x_3530_);
lean_closure_set(v___f_3542_, 28, v___x_3538_);
v___x_3543_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3530_, v___x_3538_, v___f_3542_, v___x_3507_, v___x_3507_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3544_ = _args[0];
lean_object* v___x_3545_ = _args[1];
lean_object* v_motive_3546_ = _args[2];
lean_object* v___x_3547_ = _args[3];
lean_object* v___x_3548_ = _args[4];
lean_object* v___x_3549_ = _args[5];
lean_object* v___x_3550_ = _args[6];
lean_object* v_is_3551_ = _args[7];
lean_object* v___x_3552_ = _args[8];
lean_object* v___x_3553_ = _args[9];
lean_object* v___x_3554_ = _args[10];
lean_object* v___x_3555_ = _args[11];
lean_object* v_params_3556_ = _args[12];
lean_object* v___x_3557_ = _args[13];
lean_object* v___x_3558_ = _args[14];
lean_object* v_heq_3559_ = _args[15];
lean_object* v_val_3560_ = _args[16];
lean_object* v___x_3561_ = _args[17];
lean_object* v_tail_3562_ = _args[18];
lean_object* v___x_3563_ = _args[19];
lean_object* v___x_3564_ = _args[20];
lean_object* v___x_3565_ = _args[21];
lean_object* v_declName_3566_ = _args[22];
lean_object* v_levelParams_3567_ = _args[23];
lean_object* v___x_3568_ = _args[24];
lean_object* v_numParams_3569_ = _args[25];
lean_object* v_snd_3570_ = _args[26];
lean_object* v___x_3571_ = _args[27];
lean_object* v_alts_3572_ = _args[28];
lean_object* v___y_3573_ = _args[29];
lean_object* v___y_3574_ = _args[30];
lean_object* v___y_3575_ = _args[31];
lean_object* v___y_3576_ = _args[32];
lean_object* v___y_3577_ = _args[33];
_start:
{
uint8_t v___x_16149__boxed_3578_; uint8_t v___x_16150__boxed_3579_; uint8_t v___x_16151__boxed_3580_; lean_object* v_res_3581_; 
v___x_16149__boxed_3578_ = lean_unbox(v___x_3548_);
v___x_16150__boxed_3579_ = lean_unbox(v___x_3549_);
v___x_16151__boxed_3580_ = lean_unbox(v___x_3550_);
v_res_3581_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3544_, v___x_3545_, v_motive_3546_, v___x_3547_, v___x_16149__boxed_3578_, v___x_16150__boxed_3579_, v___x_16151__boxed_3580_, v_is_3551_, v___x_3552_, v___x_3553_, v___x_3554_, v___x_3555_, v_params_3556_, v___x_3557_, v___x_3558_, v_heq_3559_, v_val_3560_, v___x_3561_, v_tail_3562_, v___x_3563_, v___x_3564_, v___x_3565_, v_declName_3566_, v_levelParams_3567_, v___x_3568_, v_numParams_3569_, v_snd_3570_, v___x_3571_, v_alts_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___x_3545_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3582_, lean_object* v_declInfos_3583_, lean_object* v_k_3584_, lean_object* v_kind_3585_, lean_object* v_x_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
uint8_t v_kind_boxed_3592_; lean_object* v_res_3593_; 
v_kind_boxed_3592_ = lean_unbox(v_kind_3585_);
v_res_3593_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3582_, v_declInfos_3583_, v_k_3584_, v_kind_boxed_3592_, v_x_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3594_, lean_object* v_k_3595_, uint8_t v_kind_3596_, lean_object* v_acc_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v_toApplicative_3604_; lean_object* v_toFunctor_3605_; lean_object* v_toSeq_3606_; lean_object* v_toSeqLeft_3607_; lean_object* v_toSeqRight_3608_; lean_object* v___f_3609_; lean_object* v___f_3610_; lean_object* v___f_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v_toApplicative_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3677_; 
v___x_3603_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3604_ = lean_ctor_get(v___x_3603_, 0);
v_toFunctor_3605_ = lean_ctor_get(v_toApplicative_3604_, 0);
v_toSeq_3606_ = lean_ctor_get(v_toApplicative_3604_, 2);
v_toSeqLeft_3607_ = lean_ctor_get(v_toApplicative_3604_, 3);
v_toSeqRight_3608_ = lean_ctor_get(v_toApplicative_3604_, 4);
v___f_3609_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3610_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3605_, 2);
v___f_3611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3611_, 0, v_toFunctor_3605_);
v___f_3612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3612_, 0, v_toFunctor_3605_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___f_3611_);
lean_ctor_set(v___x_3613_, 1, v___f_3612_);
lean_inc(v_toSeqRight_3608_);
v___f_3614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3614_, 0, v_toSeqRight_3608_);
lean_inc(v_toSeqLeft_3607_);
v___f_3615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3615_, 0, v_toSeqLeft_3607_);
lean_inc(v_toSeq_3606_);
v___f_3616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3616_, 0, v_toSeq_3606_);
v___x_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3613_);
lean_ctor_set(v___x_3617_, 1, v___f_3609_);
lean_ctor_set(v___x_3617_, 2, v___f_3616_);
lean_ctor_set(v___x_3617_, 3, v___f_3615_);
lean_ctor_set(v___x_3617_, 4, v___f_3614_);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v___f_3610_);
v___x_3619_ = l_StateRefT_x27_instMonad___redArg(v___x_3618_);
v_toApplicative_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v___x_3619_, 1);
lean_dec(v_unused_3678_);
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3677_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_toApplicative_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3677_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v_toFunctor_3624_; lean_object* v_toSeq_3625_; lean_object* v_toSeqLeft_3626_; lean_object* v_toSeqRight_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3675_; 
v_toFunctor_3624_ = lean_ctor_get(v_toApplicative_3620_, 0);
v_toSeq_3625_ = lean_ctor_get(v_toApplicative_3620_, 2);
v_toSeqLeft_3626_ = lean_ctor_get(v_toApplicative_3620_, 3);
v_toSeqRight_3627_ = lean_ctor_get(v_toApplicative_3620_, 4);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_toApplicative_3620_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v_toApplicative_3620_, 1);
lean_dec(v_unused_3676_);
v___x_3629_ = v_toApplicative_3620_;
v_isShared_3630_ = v_isSharedCheck_3675_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_toSeqRight_3627_);
lean_inc(v_toSeqLeft_3626_);
lean_inc(v_toSeq_3625_);
lean_inc(v_toFunctor_3624_);
lean_dec(v_toApplicative_3620_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3675_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___f_3631_; lean_object* v___f_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___f_3636_; lean_object* v___f_3637_; lean_object* v___f_3638_; lean_object* v___x_3640_; 
v___f_3631_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3632_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3624_);
v___f_3633_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3633_, 0, v_toFunctor_3624_);
v___f_3634_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3634_, 0, v_toFunctor_3624_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___f_3633_);
lean_ctor_set(v___x_3635_, 1, v___f_3634_);
v___f_3636_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3636_, 0, v_toSeqRight_3627_);
v___f_3637_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3637_, 0, v_toSeqLeft_3626_);
v___f_3638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3638_, 0, v_toSeq_3625_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 4, v___f_3636_);
lean_ctor_set(v___x_3629_, 3, v___f_3637_);
lean_ctor_set(v___x_3629_, 2, v___f_3638_);
lean_ctor_set(v___x_3629_, 1, v___f_3631_);
lean_ctor_set(v___x_3629_, 0, v___x_3635_);
v___x_3640_ = v___x_3629_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___f_3631_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v___f_3638_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v___f_3637_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v___f_3636_);
v___x_3640_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3642_; 
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 1, v___f_3632_);
lean_ctor_set(v___x_3622_, 0, v___x_3640_);
v___x_3642_ = v___x_3622_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___f_3632_);
v___x_3642_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3643_ = lean_array_get_size(v_acc_3597_);
v___x_3644_ = lean_array_get_size(v_declInfos_3594_);
v___x_3645_ = lean_nat_dec_lt(v___x_3643_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; 
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_declInfos_3594_);
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
lean_inc(v___y_3599_);
lean_inc_ref(v___y_3598_);
v___x_3646_ = lean_apply_6(v_k_3595_, v_acc_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, lean_box(0));
return v___x_3646_;
}
else
{
lean_object* v___f_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v_snd_3655_; lean_object* v_fst_3656_; lean_object* v_fst_3657_; lean_object* v_snd_3658_; lean_object* v___x_3659_; 
v___f_3647_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3647_, 0, v___x_3642_);
v___x_3648_ = lean_box(0);
v___x_3649_ = 0;
v___f_3650_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3650_, 0, v___f_3647_);
v___x_3651_ = lean_box(v___x_3649_);
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v___f_3650_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3648_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_array_get(v___x_3653_, v_declInfos_3594_, v___x_3643_);
lean_dec_ref(v___x_3653_);
v_snd_3655_ = lean_ctor_get(v___x_3654_, 1);
lean_inc(v_snd_3655_);
v_fst_3656_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_fst_3656_);
lean_dec(v___x_3654_);
v_fst_3657_ = lean_ctor_get(v_snd_3655_, 0);
lean_inc(v_fst_3657_);
v_snd_3658_ = lean_ctor_get(v_snd_3655_, 1);
lean_inc(v_snd_3658_);
lean_dec(v_snd_3655_);
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
lean_inc(v___y_3599_);
lean_inc_ref(v___y_3598_);
lean_inc_ref(v_acc_3597_);
v___x_3659_ = lean_apply_6(v_snd_3658_, v_acc_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, lean_box(0));
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; uint8_t v___x_3663_; lean_object* v___x_3664_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref(v___x_3659_);
v___x_3661_ = lean_box(v_kind_3596_);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3662_, 0, v_acc_3597_);
lean_closure_set(v___f_3662_, 1, v_declInfos_3594_);
lean_closure_set(v___f_3662_, 2, v_k_3595_);
lean_closure_set(v___f_3662_, 3, v___x_3661_);
v___x_3663_ = lean_unbox(v_fst_3657_);
lean_dec(v_fst_3657_);
v___x_3664_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3656_, v___x_3663_, v_a_3660_, v___f_3662_, v_kind_3596_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3664_;
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec(v_fst_3657_);
lean_dec(v_fst_3656_);
lean_dec_ref(v_acc_3597_);
lean_dec_ref(v_k_3595_);
lean_dec_ref(v_declInfos_3594_);
v_a_3665_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3659_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3659_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3679_, lean_object* v_declInfos_3680_, lean_object* v_k_3681_, uint8_t v_kind_3682_, lean_object* v_x_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_array_push(v_acc_3679_, v_x_3683_);
v___x_3690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3680_, v_k_3681_, v_kind_3682_, v___x_3689_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3691_, lean_object* v_k_3692_, lean_object* v_kind_3693_, lean_object* v_acc_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v_kind_boxed_3700_; lean_object* v_res_3701_; 
v_kind_boxed_3700_ = lean_unbox(v_kind_3693_);
v_res_3701_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3691_, v_k_3692_, v_kind_boxed_3700_, v_acc_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3702_, lean_object* v_k_3703_, uint8_t v_kind_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3711_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3702_, v_k_3703_, v_kind_3704_, v___x_3710_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3712_, lean_object* v_k_3713_, lean_object* v_kind_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
uint8_t v_kind_boxed_3720_; lean_object* v_res_3721_; 
v_kind_boxed_3720_ = lean_unbox(v_kind_3714_);
v_res_3721_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3712_, v_k_3713_, v_kind_boxed_3720_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3722_, lean_object* v_k_3723_, uint8_t v_kind_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
size_t v_sz_3730_; size_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_sz_3730_ = lean_array_size(v_declInfos_3722_);
v___x_3731_ = ((size_t)0ULL);
v___x_3732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3730_, v___x_3731_, v_declInfos_3722_);
v___x_3733_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3732_, v_k_3723_, v_kind_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3734_, lean_object* v_k_3735_, lean_object* v_kind_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v_kind_boxed_3742_; lean_object* v_res_3743_; 
v_kind_boxed_3742_ = lean_unbox(v_kind_3736_);
v_res_3743_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3734_, v_k_3735_, v_kind_boxed_3742_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3744_, lean_object* v_k_3745_, uint8_t v_kind_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
size_t v_sz_3752_; size_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_sz_3752_ = lean_array_size(v_declInfos_3744_);
v___x_3753_ = ((size_t)0ULL);
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3752_, v___x_3753_, v_declInfos_3744_);
v___x_3755_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3754_, v_k_3745_, v_kind_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3756_, lean_object* v_k_3757_, lean_object* v_kind_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v_kind_boxed_3764_; lean_object* v_res_3765_; 
v_kind_boxed_3764_ = lean_unbox(v_kind_3758_);
v_res_3765_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3756_, v_k_3757_, v_kind_boxed_3764_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
return v_res_3765_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_box(0);
v___x_3769_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3770_ = l_Lean_mkConst(v___x_3769_, v___x_3768_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v_j_3771_, lean_object* v___x_3772_, lean_object* v_motive_3773_, uint8_t v_isZero_3774_, uint8_t v___x_3775_, uint8_t v___x_3776_, lean_object* v___x_3777_, lean_object* v___x_3778_, lean_object* v___x_3779_, lean_object* v_zs12_3780_, lean_object* v_is_3781_, lean_object* v_fields1_3782_, lean_object* v_fields2_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v_e_3799_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
lean_inc(v_j_3771_);
v___x_3809_ = l_Lean_mkNatLit(v_j_3771_);
v___x_3810_ = l_Lean_Meta_mkEqRefl(v___x_3809_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref(v___x_3810_);
lean_inc_ref(v___x_3772_);
v___x_3812_ = l_Lean_mkAppN(v___x_3772_, v_fields1_3782_);
v___x_3813_ = l_Lean_mkAppN(v___x_3772_, v_fields2_3783_);
v___x_3814_ = lean_unsigned_to_nat(3u);
v___x_3815_ = lean_mk_empty_array_with_capacity(v___x_3814_);
v___x_3816_ = lean_array_push(v___x_3815_, v___x_3812_);
v___x_3817_ = lean_array_push(v___x_3816_, v___x_3813_);
v___x_3818_ = lean_array_push(v___x_3817_, v_a_3811_);
v___x_3819_ = l_Array_append___redArg(v_is_3781_, v___x_3818_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = l_Lean_mkAppN(v_motive_3773_, v___x_3819_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = l_Lean_Meta_mkForallFVars(v_zs12_3780_, v___x_3820_, v_isZero_3774_, v___x_3775_, v___x_3775_, v___x_3776_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = lean_array_get_size(v_zs12_3780_);
v___x_3824_ = lean_nat_dec_eq(v___x_3823_, v___x_3777_);
if (v___x_3824_ == 0)
{
v_e_3799_ = v_a_3822_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3826_ = l_Lean_mkArrow(v___x_3825_, v_a_3822_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref(v___x_3826_);
v_e_3799_ = v_a_3827_;
goto v___jp_3798_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v___x_3778_);
lean_dec(v___x_3777_);
lean_dec(v_j_3771_);
v_a_3828_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3826_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3826_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec(v___x_3778_);
lean_dec(v___x_3777_);
lean_dec(v_j_3771_);
v_a_3836_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3821_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3821_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_is_3781_);
lean_dec(v___x_3778_);
lean_dec(v___x_3777_);
lean_dec_ref(v_motive_3773_);
lean_dec_ref(v___x_3772_);
lean_dec(v_j_3771_);
v_a_3844_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3810_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3810_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
v___jp_3789_:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3792_ = lean_array_get_size(v_zs12_3780_);
v___x_3793_ = lean_nat_dec_eq(v___x_3792_, v___x_3777_);
v___x_3794_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3794_, 0, v___x_3792_);
lean_ctor_set(v___x_3794_, 1, v___x_3777_);
lean_ctor_set_uint8(v___x_3794_, sizeof(void*)*2, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___y_3791_);
lean_ctor_set(v___x_3795_, 1, v___y_3790_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v___x_3794_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
v___jp_3798_:
{
if (lean_obj_tag(v___x_3778_) == 1)
{
lean_object* v_str_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec(v_j_3771_);
v_str_3800_ = lean_ctor_get(v___x_3778_, 1);
lean_inc_ref(v_str_3800_);
lean_dec_ref(v___x_3778_);
v___x_3801_ = lean_box(0);
v___x_3802_ = l_Lean_Name_str___override(v___x_3801_, v_str_3800_);
v___y_3790_ = v_e_3799_;
v___y_3791_ = v___x_3802_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_dec(v___x_3778_);
v___x_3803_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3804_ = lean_nat_add(v_j_3771_, v___x_3779_);
lean_dec(v_j_3771_);
v___x_3805_ = l_Nat_reprFast(v___x_3804_);
v___x_3806_ = lean_string_append(v___x_3803_, v___x_3805_);
lean_dec_ref(v___x_3805_);
v___x_3807_ = lean_box(0);
v___x_3808_ = l_Lean_Name_str___override(v___x_3807_, v___x_3806_);
v___y_3790_ = v_e_3799_;
v___y_3791_ = v___x_3808_;
goto v___jp_3789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_j_3852_ = _args[0];
lean_object* v___x_3853_ = _args[1];
lean_object* v_motive_3854_ = _args[2];
lean_object* v_isZero_3855_ = _args[3];
lean_object* v___x_3856_ = _args[4];
lean_object* v___x_3857_ = _args[5];
lean_object* v___x_3858_ = _args[6];
lean_object* v___x_3859_ = _args[7];
lean_object* v___x_3860_ = _args[8];
lean_object* v_zs12_3861_ = _args[9];
lean_object* v_is_3862_ = _args[10];
lean_object* v_fields1_3863_ = _args[11];
lean_object* v_fields2_3864_ = _args[12];
lean_object* v___y_3865_ = _args[13];
lean_object* v___y_3866_ = _args[14];
lean_object* v___y_3867_ = _args[15];
lean_object* v___y_3868_ = _args[16];
lean_object* v___y_3869_ = _args[17];
_start:
{
uint8_t v_isZero_boxed_3870_; uint8_t v___x_16487__boxed_3871_; uint8_t v___x_16488__boxed_3872_; lean_object* v_res_3873_; 
v_isZero_boxed_3870_ = lean_unbox(v_isZero_3855_);
v___x_16487__boxed_3871_ = lean_unbox(v___x_3856_);
v___x_16488__boxed_3872_ = lean_unbox(v___x_3857_);
v_res_3873_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v_j_3852_, v___x_3853_, v_motive_3854_, v_isZero_boxed_3870_, v___x_16487__boxed_3871_, v___x_16488__boxed_3872_, v___x_3858_, v___x_3859_, v___x_3860_, v_zs12_3861_, v_is_3862_, v_fields1_3863_, v_fields2_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec_ref(v_fields2_3864_);
lean_dec_ref(v_fields1_3863_);
lean_dec_ref(v_zs12_3861_);
lean_dec(v___x_3860_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3874_, lean_object* v_params_3875_, lean_object* v_motive_3876_, lean_object* v_as_3877_, lean_object* v_i_3878_, lean_object* v_j_3879_, lean_object* v_bs_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_zero_3886_; uint8_t v_isZero_3887_; 
v_zero_3886_ = lean_unsigned_to_nat(0u);
v_isZero_3887_ = lean_nat_dec_eq(v_i_3878_, v_zero_3886_);
if (v_isZero_3887_ == 1)
{
lean_object* v___x_3888_; 
lean_dec(v_j_3879_);
lean_dec(v_i_3878_);
lean_dec_ref(v_motive_3876_);
lean_dec(v_tail_3874_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_bs_3880_);
return v___x_3888_;
}
else
{
lean_object* v___x_3889_; uint8_t v___x_3890_; uint8_t v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___f_3898_; lean_object* v___x_3899_; 
v___x_3889_ = lean_unsigned_to_nat(1u);
v___x_3890_ = 1;
v___x_3891_ = 1;
v___x_3892_ = lean_array_fget_borrowed(v_as_3877_, v_j_3879_);
lean_inc(v_tail_3874_);
lean_inc_n(v___x_3892_, 2);
v___x_3893_ = l_Lean_mkConst(v___x_3892_, v_tail_3874_);
v___x_3894_ = l_Lean_mkAppN(v___x_3893_, v_params_3875_);
v___x_3895_ = lean_box(v_isZero_3887_);
v___x_3896_ = lean_box(v___x_3890_);
v___x_3897_ = lean_box(v___x_3891_);
lean_inc_ref(v_motive_3876_);
lean_inc_ref(v___x_3894_);
lean_inc(v_j_3879_);
v___f_3898_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3898_, 0, v_j_3879_);
lean_closure_set(v___f_3898_, 1, v___x_3894_);
lean_closure_set(v___f_3898_, 2, v_motive_3876_);
lean_closure_set(v___f_3898_, 3, v___x_3895_);
lean_closure_set(v___f_3898_, 4, v___x_3896_);
lean_closure_set(v___f_3898_, 5, v___x_3897_);
lean_closure_set(v___f_3898_, 6, v_zero_3886_);
lean_closure_set(v___f_3898_, 7, v___x_3892_);
lean_closure_set(v___f_3898_, 8, v___x_3889_);
v___x_3899_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3894_, v___f_3898_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v_n_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3899_);
v_n_3901_ = lean_nat_sub(v_i_3878_, v___x_3889_);
lean_dec(v_i_3878_);
v___x_3902_ = lean_nat_add(v_j_3879_, v___x_3889_);
lean_dec(v_j_3879_);
v___x_3903_ = lean_array_push(v_bs_3880_, v_a_3900_);
v_i_3878_ = v_n_3901_;
v_j_3879_ = v___x_3902_;
v_bs_3880_ = v___x_3903_;
goto _start;
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec_ref(v_bs_3880_);
lean_dec(v_j_3879_);
lean_dec(v_i_3878_);
lean_dec_ref(v_motive_3876_);
lean_dec(v_tail_3874_);
v_a_3905_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3899_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3899_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3913_, lean_object* v_params_3914_, lean_object* v_motive_3915_, lean_object* v_as_3916_, lean_object* v_i_3917_, lean_object* v_j_3918_, lean_object* v_bs_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3913_, v_params_3914_, v_motive_3915_, v_as_3916_, v_i_3917_, v_j_3918_, v_bs_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec_ref(v_as_3916_);
lean_dec_ref(v_params_3914_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3926_, lean_object* v_tail_3927_, lean_object* v_params_3928_, lean_object* v___x_3929_, lean_object* v_numIndices_3930_, lean_object* v___x_3931_, lean_object* v___x_3932_, uint8_t v___x_3933_, uint8_t v___x_3934_, uint8_t v___x_3935_, lean_object* v_is_3936_, lean_object* v___x_3937_, lean_object* v___x_3938_, lean_object* v___x_3939_, lean_object* v___x_3940_, lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v_heq_3943_, lean_object* v_val_3944_, lean_object* v___x_3945_, lean_object* v_declName_3946_, lean_object* v_levelParams_3947_, lean_object* v___x_3948_, lean_object* v_numParams_3949_, lean_object* v___x_3950_, lean_object* v_motive_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3957_ = lean_array_mk(v_ctors_3926_);
v___x_3958_ = lean_array_get_size(v___x_3957_);
v___x_3959_ = lean_mk_empty_array_with_capacity(v___x_3958_);
lean_inc(v___x_3929_);
lean_inc_ref(v_motive_3951_);
lean_inc(v_tail_3927_);
v___x_3960_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3927_, v_params_3928_, v_motive_3951_, v___x_3957_, v___x_3958_, v___x_3929_, v___x_3959_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; lean_object* v_fst_3963_; lean_object* v_snd_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
v___x_3962_ = l_Array_unzip___redArg(v_a_3961_);
lean_dec(v_a_3961_);
v_fst_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_fst_3963_);
v_snd_3964_ = lean_ctor_get(v___x_3962_, 1);
lean_inc(v_snd_3964_);
lean_dec_ref(v___x_3962_);
v___x_3965_ = lean_box(v___x_3933_);
v___x_3966_ = lean_box(v___x_3934_);
v___x_3967_ = lean_box(v___x_3935_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 34, 28);
lean_closure_set(v___f_3968_, 0, v_numIndices_3930_);
lean_closure_set(v___f_3968_, 1, v___x_3931_);
lean_closure_set(v___f_3968_, 2, v_motive_3951_);
lean_closure_set(v___f_3968_, 3, v___x_3932_);
lean_closure_set(v___f_3968_, 4, v___x_3965_);
lean_closure_set(v___f_3968_, 5, v___x_3966_);
lean_closure_set(v___f_3968_, 6, v___x_3967_);
lean_closure_set(v___f_3968_, 7, v_is_3936_);
lean_closure_set(v___f_3968_, 8, v___x_3937_);
lean_closure_set(v___f_3968_, 9, v___x_3938_);
lean_closure_set(v___f_3968_, 10, v___x_3939_);
lean_closure_set(v___f_3968_, 11, v___x_3940_);
lean_closure_set(v___f_3968_, 12, v_params_3928_);
lean_closure_set(v___f_3968_, 13, v___x_3941_);
lean_closure_set(v___f_3968_, 14, v___x_3942_);
lean_closure_set(v___f_3968_, 15, v_heq_3943_);
lean_closure_set(v___f_3968_, 16, v_val_3944_);
lean_closure_set(v___f_3968_, 17, v___x_3958_);
lean_closure_set(v___f_3968_, 18, v_tail_3927_);
lean_closure_set(v___f_3968_, 19, v___x_3957_);
lean_closure_set(v___f_3968_, 20, v___x_3929_);
lean_closure_set(v___f_3968_, 21, v___x_3945_);
lean_closure_set(v___f_3968_, 22, v_declName_3946_);
lean_closure_set(v___f_3968_, 23, v_levelParams_3947_);
lean_closure_set(v___f_3968_, 24, v___x_3948_);
lean_closure_set(v___f_3968_, 25, v_numParams_3949_);
lean_closure_set(v___f_3968_, 26, v_snd_3964_);
lean_closure_set(v___f_3968_, 27, v___x_3950_);
v___x_3969_ = 0;
v___x_3970_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3963_, v___f_3968_, v___x_3969_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3970_;
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_motive_3951_);
lean_dec_ref(v___x_3950_);
lean_dec(v_numParams_3949_);
lean_dec(v___x_3948_);
lean_dec(v_levelParams_3947_);
lean_dec(v_declName_3946_);
lean_dec_ref(v___x_3945_);
lean_dec_ref(v_val_3944_);
lean_dec_ref(v_heq_3943_);
lean_dec_ref(v___x_3942_);
lean_dec_ref(v___x_3941_);
lean_dec(v___x_3940_);
lean_dec(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
lean_dec_ref(v_is_3936_);
lean_dec_ref(v___x_3932_);
lean_dec(v___x_3931_);
lean_dec(v_numIndices_3930_);
lean_dec(v___x_3929_);
lean_dec_ref(v_params_3928_);
lean_dec(v_tail_3927_);
v_a_3971_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3960_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3960_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_3979_ = _args[0];
lean_object* v_tail_3980_ = _args[1];
lean_object* v_params_3981_ = _args[2];
lean_object* v___x_3982_ = _args[3];
lean_object* v_numIndices_3983_ = _args[4];
lean_object* v___x_3984_ = _args[5];
lean_object* v___x_3985_ = _args[6];
lean_object* v___x_3986_ = _args[7];
lean_object* v___x_3987_ = _args[8];
lean_object* v___x_3988_ = _args[9];
lean_object* v_is_3989_ = _args[10];
lean_object* v___x_3990_ = _args[11];
lean_object* v___x_3991_ = _args[12];
lean_object* v___x_3992_ = _args[13];
lean_object* v___x_3993_ = _args[14];
lean_object* v___x_3994_ = _args[15];
lean_object* v___x_3995_ = _args[16];
lean_object* v_heq_3996_ = _args[17];
lean_object* v_val_3997_ = _args[18];
lean_object* v___x_3998_ = _args[19];
lean_object* v_declName_3999_ = _args[20];
lean_object* v_levelParams_4000_ = _args[21];
lean_object* v___x_4001_ = _args[22];
lean_object* v_numParams_4002_ = _args[23];
lean_object* v___x_4003_ = _args[24];
lean_object* v_motive_4004_ = _args[25];
lean_object* v___y_4005_ = _args[26];
lean_object* v___y_4006_ = _args[27];
lean_object* v___y_4007_ = _args[28];
lean_object* v___y_4008_ = _args[29];
lean_object* v___y_4009_ = _args[30];
_start:
{
uint8_t v___x_16721__boxed_4010_; uint8_t v___x_16722__boxed_4011_; uint8_t v___x_16723__boxed_4012_; lean_object* v_res_4013_; 
v___x_16721__boxed_4010_ = lean_unbox(v___x_3986_);
v___x_16722__boxed_4011_ = lean_unbox(v___x_3987_);
v___x_16723__boxed_4012_ = lean_unbox(v___x_3988_);
v_res_4013_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_3979_, v_tail_3980_, v_params_3981_, v___x_3982_, v_numIndices_3983_, v___x_3984_, v___x_3985_, v___x_16721__boxed_4010_, v___x_16722__boxed_4011_, v___x_16723__boxed_4012_, v_is_3989_, v___x_3990_, v___x_3991_, v___x_3992_, v___x_3993_, v___x_3994_, v___x_3995_, v_heq_3996_, v_val_3997_, v___x_3998_, v_declName_3999_, v_levelParams_4000_, v___x_4001_, v_numParams_4002_, v___x_4003_, v_motive_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4014_, lean_object* v___x_4015_, lean_object* v_is_4016_, lean_object* v_head_4017_, lean_object* v_ctors_4018_, lean_object* v_tail_4019_, lean_object* v_params_4020_, lean_object* v___x_4021_, lean_object* v_numIndices_4022_, lean_object* v___x_4023_, lean_object* v___x_4024_, lean_object* v___x_4025_, lean_object* v___x_4026_, lean_object* v___x_4027_, lean_object* v_val_4028_, lean_object* v___x_4029_, lean_object* v_declName_4030_, lean_object* v_levelParams_4031_, lean_object* v_numParams_4032_, lean_object* v___x_4033_, lean_object* v_heq_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; uint8_t v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; 
v___x_4040_ = lean_unsigned_to_nat(3u);
v___x_4041_ = lean_mk_empty_array_with_capacity(v___x_4040_);
lean_inc_ref(v___x_4014_);
v___x_4042_ = lean_array_push(v___x_4041_, v___x_4014_);
lean_inc_ref(v___x_4015_);
v___x_4043_ = lean_array_push(v___x_4042_, v___x_4015_);
lean_inc_ref(v_heq_4034_);
v___x_4044_ = lean_array_push(v___x_4043_, v_heq_4034_);
lean_inc_ref(v_is_4016_);
v___x_4045_ = l_Array_append___redArg(v_is_4016_, v___x_4044_);
lean_dec_ref(v___x_4044_);
v___x_4046_ = l_Lean_mkSort(v_head_4017_);
v___x_4047_ = 0;
v___x_4048_ = 1;
v___x_4049_ = 1;
v___x_4050_ = l_Lean_Meta_mkForallFVars(v___x_4045_, v___x_4046_, v___x_4047_, v___x_4048_, v___x_4048_, v___x_4049_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___f_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = lean_box(v___x_4047_);
v___x_4053_ = lean_box(v___x_4048_);
v___x_4054_ = lean_box(v___x_4049_);
v___f_4055_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4055_, 0, v_ctors_4018_);
lean_closure_set(v___f_4055_, 1, v_tail_4019_);
lean_closure_set(v___f_4055_, 2, v_params_4020_);
lean_closure_set(v___f_4055_, 3, v___x_4021_);
lean_closure_set(v___f_4055_, 4, v_numIndices_4022_);
lean_closure_set(v___f_4055_, 5, v___x_4023_);
lean_closure_set(v___f_4055_, 6, v___x_4045_);
lean_closure_set(v___f_4055_, 7, v___x_4052_);
lean_closure_set(v___f_4055_, 8, v___x_4053_);
lean_closure_set(v___f_4055_, 9, v___x_4054_);
lean_closure_set(v___f_4055_, 10, v_is_4016_);
lean_closure_set(v___f_4055_, 11, v___x_4015_);
lean_closure_set(v___f_4055_, 12, v___x_4014_);
lean_closure_set(v___f_4055_, 13, v___x_4024_);
lean_closure_set(v___f_4055_, 14, v___x_4025_);
lean_closure_set(v___f_4055_, 15, v___x_4026_);
lean_closure_set(v___f_4055_, 16, v___x_4027_);
lean_closure_set(v___f_4055_, 17, v_heq_4034_);
lean_closure_set(v___f_4055_, 18, v_val_4028_);
lean_closure_set(v___f_4055_, 19, v___x_4029_);
lean_closure_set(v___f_4055_, 20, v_declName_4030_);
lean_closure_set(v___f_4055_, 21, v_levelParams_4031_);
lean_closure_set(v___f_4055_, 22, v___x_4040_);
lean_closure_set(v___f_4055_, 23, v_numParams_4032_);
lean_closure_set(v___f_4055_, 24, v___x_4033_);
v___x_4056_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4057_ = 0;
v___x_4058_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4056_, v___x_4049_, v_a_4051_, v___f_4055_, v___x_4057_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4058_;
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec_ref(v___x_4045_);
lean_dec_ref(v_heq_4034_);
lean_dec_ref(v___x_4033_);
lean_dec(v_numParams_4032_);
lean_dec(v_levelParams_4031_);
lean_dec(v_declName_4030_);
lean_dec_ref(v___x_4029_);
lean_dec_ref(v_val_4028_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v___x_4026_);
lean_dec(v___x_4025_);
lean_dec(v___x_4024_);
lean_dec(v___x_4023_);
lean_dec(v_numIndices_4022_);
lean_dec(v___x_4021_);
lean_dec_ref(v_params_4020_);
lean_dec(v_tail_4019_);
lean_dec(v_ctors_4018_);
lean_dec_ref(v_is_4016_);
lean_dec_ref(v___x_4015_);
lean_dec_ref(v___x_4014_);
v_a_4059_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4050_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4050_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4067_ = _args[0];
lean_object* v___x_4068_ = _args[1];
lean_object* v_is_4069_ = _args[2];
lean_object* v_head_4070_ = _args[3];
lean_object* v_ctors_4071_ = _args[4];
lean_object* v_tail_4072_ = _args[5];
lean_object* v_params_4073_ = _args[6];
lean_object* v___x_4074_ = _args[7];
lean_object* v_numIndices_4075_ = _args[8];
lean_object* v___x_4076_ = _args[9];
lean_object* v___x_4077_ = _args[10];
lean_object* v___x_4078_ = _args[11];
lean_object* v___x_4079_ = _args[12];
lean_object* v___x_4080_ = _args[13];
lean_object* v_val_4081_ = _args[14];
lean_object* v___x_4082_ = _args[15];
lean_object* v_declName_4083_ = _args[16];
lean_object* v_levelParams_4084_ = _args[17];
lean_object* v_numParams_4085_ = _args[18];
lean_object* v___x_4086_ = _args[19];
lean_object* v_heq_4087_ = _args[20];
lean_object* v___y_4088_ = _args[21];
lean_object* v___y_4089_ = _args[22];
lean_object* v___y_4090_ = _args[23];
lean_object* v___y_4091_ = _args[24];
lean_object* v___y_4092_ = _args[25];
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4067_, v___x_4068_, v_is_4069_, v_head_4070_, v_ctors_4071_, v_tail_4072_, v_params_4073_, v___x_4074_, v_numIndices_4075_, v___x_4076_, v___x_4077_, v___x_4078_, v___x_4079_, v___x_4080_, v_val_4081_, v___x_4082_, v_declName_4083_, v_levelParams_4084_, v_numParams_4085_, v___x_4086_, v_heq_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4094_, lean_object* v_x1_4095_, lean_object* v_indName_4096_, lean_object* v_tail_4097_, lean_object* v_params_4098_, lean_object* v_is_4099_, lean_object* v___x_4100_, lean_object* v_head_4101_, lean_object* v_ctors_4102_, lean_object* v_numIndices_4103_, lean_object* v___x_4104_, lean_object* v___x_4105_, lean_object* v_val_4106_, lean_object* v_declName_4107_, lean_object* v_levelParams_4108_, lean_object* v_numParams_4109_, lean_object* v___x_4110_, lean_object* v_x2_4111_, lean_object* v_x_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4118_ = lean_unsigned_to_nat(0u);
v___x_4119_ = lean_array_get_borrowed(v___x_4094_, v_x1_4095_, v___x_4118_);
v___x_4120_ = lean_array_get_borrowed(v___x_4094_, v_x2_4111_, v___x_4118_);
v___x_4121_ = l_mkCtorIdxName(v_indName_4096_);
lean_inc(v_tail_4097_);
v___x_4122_ = l_Lean_mkConst(v___x_4121_, v_tail_4097_);
lean_inc_ref(v_params_4098_);
v___x_4123_ = l_Array_append___redArg(v_params_4098_, v_is_4099_);
v___x_4124_ = lean_mk_empty_array_with_capacity(v___x_4100_);
lean_inc(v___x_4119_);
lean_inc_ref_n(v___x_4124_, 2);
v___x_4125_ = lean_array_push(v___x_4124_, v___x_4119_);
lean_inc_ref(v___x_4123_);
v___x_4126_ = l_Array_append___redArg(v___x_4123_, v___x_4125_);
lean_inc_ref(v___x_4122_);
v___x_4127_ = l_Lean_mkAppN(v___x_4122_, v___x_4126_);
lean_dec_ref(v___x_4126_);
lean_inc(v___x_4120_);
v___x_4128_ = lean_array_push(v___x_4124_, v___x_4120_);
v___x_4129_ = l_Array_append___redArg(v___x_4123_, v___x_4128_);
v___x_4130_ = l_Lean_mkAppN(v___x_4122_, v___x_4129_);
lean_dec_ref(v___x_4129_);
v___x_4131_ = l_Lean_Meta_mkEq(v___x_4127_, v___x_4130_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___f_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref(v___x_4131_);
lean_inc(v___x_4120_);
lean_inc(v___x_4119_);
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4133_, 0, v___x_4119_);
lean_closure_set(v___f_4133_, 1, v___x_4120_);
lean_closure_set(v___f_4133_, 2, v_is_4099_);
lean_closure_set(v___f_4133_, 3, v_head_4101_);
lean_closure_set(v___f_4133_, 4, v_ctors_4102_);
lean_closure_set(v___f_4133_, 5, v_tail_4097_);
lean_closure_set(v___f_4133_, 6, v_params_4098_);
lean_closure_set(v___f_4133_, 7, v___x_4118_);
lean_closure_set(v___f_4133_, 8, v_numIndices_4103_);
lean_closure_set(v___f_4133_, 9, v___x_4100_);
lean_closure_set(v___f_4133_, 10, v___x_4104_);
lean_closure_set(v___f_4133_, 11, v___x_4105_);
lean_closure_set(v___f_4133_, 12, v___x_4125_);
lean_closure_set(v___f_4133_, 13, v___x_4128_);
lean_closure_set(v___f_4133_, 14, v_val_4106_);
lean_closure_set(v___f_4133_, 15, v___x_4124_);
lean_closure_set(v___f_4133_, 16, v_declName_4107_);
lean_closure_set(v___f_4133_, 17, v_levelParams_4108_);
lean_closure_set(v___f_4133_, 18, v_numParams_4109_);
lean_closure_set(v___f_4133_, 19, v___x_4110_);
v___x_4134_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4135_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4134_, v_a_4132_, v___f_4133_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
return v___x_4135_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v___x_4128_);
lean_dec_ref(v___x_4125_);
lean_dec_ref(v___x_4124_);
lean_dec_ref(v___x_4110_);
lean_dec(v_numParams_4109_);
lean_dec(v_levelParams_4108_);
lean_dec(v_declName_4107_);
lean_dec_ref(v_val_4106_);
lean_dec(v___x_4105_);
lean_dec(v___x_4104_);
lean_dec(v_numIndices_4103_);
lean_dec(v_ctors_4102_);
lean_dec(v_head_4101_);
lean_dec(v___x_4100_);
lean_dec_ref(v_is_4099_);
lean_dec_ref(v_params_4098_);
lean_dec(v_tail_4097_);
v_a_4136_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4131_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4131_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4144_ = _args[0];
lean_object* v_x1_4145_ = _args[1];
lean_object* v_indName_4146_ = _args[2];
lean_object* v_tail_4147_ = _args[3];
lean_object* v_params_4148_ = _args[4];
lean_object* v_is_4149_ = _args[5];
lean_object* v___x_4150_ = _args[6];
lean_object* v_head_4151_ = _args[7];
lean_object* v_ctors_4152_ = _args[8];
lean_object* v_numIndices_4153_ = _args[9];
lean_object* v___x_4154_ = _args[10];
lean_object* v___x_4155_ = _args[11];
lean_object* v_val_4156_ = _args[12];
lean_object* v_declName_4157_ = _args[13];
lean_object* v_levelParams_4158_ = _args[14];
lean_object* v_numParams_4159_ = _args[15];
lean_object* v___x_4160_ = _args[16];
lean_object* v_x2_4161_ = _args[17];
lean_object* v_x_4162_ = _args[18];
lean_object* v___y_4163_ = _args[19];
lean_object* v___y_4164_ = _args[20];
lean_object* v___y_4165_ = _args[21];
lean_object* v___y_4166_ = _args[22];
lean_object* v___y_4167_ = _args[23];
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4144_, v_x1_4145_, v_indName_4146_, v_tail_4147_, v_params_4148_, v_is_4149_, v___x_4150_, v_head_4151_, v_ctors_4152_, v_numIndices_4153_, v___x_4154_, v___x_4155_, v_val_4156_, v_declName_4157_, v_levelParams_4158_, v_numParams_4159_, v___x_4160_, v_x2_4161_, v_x_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec_ref(v_x_4162_);
lean_dec_ref(v_x2_4161_);
lean_dec_ref(v_x1_4145_);
lean_dec_ref(v___x_4144_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4169_, lean_object* v_indName_4170_, lean_object* v_tail_4171_, lean_object* v_params_4172_, lean_object* v_is_4173_, lean_object* v___x_4174_, lean_object* v_head_4175_, lean_object* v_ctors_4176_, lean_object* v_numIndices_4177_, lean_object* v___x_4178_, lean_object* v___x_4179_, lean_object* v_val_4180_, lean_object* v_declName_4181_, lean_object* v_levelParams_4182_, lean_object* v_numParams_4183_, lean_object* v___x_4184_, lean_object* v_t_4185_, lean_object* v___x_4186_, lean_object* v_x1_4187_, lean_object* v_x_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___f_4194_; uint8_t v___x_4195_; lean_object* v___x_4196_; 
v___f_4194_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4194_, 0, v___x_4169_);
lean_closure_set(v___f_4194_, 1, v_x1_4187_);
lean_closure_set(v___f_4194_, 2, v_indName_4170_);
lean_closure_set(v___f_4194_, 3, v_tail_4171_);
lean_closure_set(v___f_4194_, 4, v_params_4172_);
lean_closure_set(v___f_4194_, 5, v_is_4173_);
lean_closure_set(v___f_4194_, 6, v___x_4174_);
lean_closure_set(v___f_4194_, 7, v_head_4175_);
lean_closure_set(v___f_4194_, 8, v_ctors_4176_);
lean_closure_set(v___f_4194_, 9, v_numIndices_4177_);
lean_closure_set(v___f_4194_, 10, v___x_4178_);
lean_closure_set(v___f_4194_, 11, v___x_4179_);
lean_closure_set(v___f_4194_, 12, v_val_4180_);
lean_closure_set(v___f_4194_, 13, v_declName_4181_);
lean_closure_set(v___f_4194_, 14, v_levelParams_4182_);
lean_closure_set(v___f_4194_, 15, v_numParams_4183_);
lean_closure_set(v___f_4194_, 16, v___x_4184_);
v___x_4195_ = 0;
v___x_4196_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4185_, v___x_4186_, v___f_4194_, v___x_4195_, v___x_4195_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4197_ = _args[0];
lean_object* v_indName_4198_ = _args[1];
lean_object* v_tail_4199_ = _args[2];
lean_object* v_params_4200_ = _args[3];
lean_object* v_is_4201_ = _args[4];
lean_object* v___x_4202_ = _args[5];
lean_object* v_head_4203_ = _args[6];
lean_object* v_ctors_4204_ = _args[7];
lean_object* v_numIndices_4205_ = _args[8];
lean_object* v___x_4206_ = _args[9];
lean_object* v___x_4207_ = _args[10];
lean_object* v_val_4208_ = _args[11];
lean_object* v_declName_4209_ = _args[12];
lean_object* v_levelParams_4210_ = _args[13];
lean_object* v_numParams_4211_ = _args[14];
lean_object* v___x_4212_ = _args[15];
lean_object* v_t_4213_ = _args[16];
lean_object* v___x_4214_ = _args[17];
lean_object* v_x1_4215_ = _args[18];
lean_object* v_x_4216_ = _args[19];
lean_object* v___y_4217_ = _args[20];
lean_object* v___y_4218_ = _args[21];
lean_object* v___y_4219_ = _args[22];
lean_object* v___y_4220_ = _args[23];
lean_object* v___y_4221_ = _args[24];
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4197_, v_indName_4198_, v_tail_4199_, v_params_4200_, v_is_4201_, v___x_4202_, v_head_4203_, v_ctors_4204_, v_numIndices_4205_, v___x_4206_, v___x_4207_, v_val_4208_, v_declName_4209_, v_levelParams_4210_, v_numParams_4211_, v___x_4212_, v_t_4213_, v___x_4214_, v_x1_4215_, v_x_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v_x_4216_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4223_, lean_object* v_indName_4224_, lean_object* v_tail_4225_, lean_object* v_params_4226_, lean_object* v_head_4227_, lean_object* v_ctors_4228_, lean_object* v_numIndices_4229_, lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v_val_4232_, lean_object* v_declName_4233_, lean_object* v_levelParams_4234_, lean_object* v_numParams_4235_, lean_object* v___x_4236_, lean_object* v_is_4237_, lean_object* v_t_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___f_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; 
v___x_4244_ = lean_unsigned_to_nat(1u);
v___x_4245_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4238_);
v___f_4246_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4246_, 0, v___x_4223_);
lean_closure_set(v___f_4246_, 1, v_indName_4224_);
lean_closure_set(v___f_4246_, 2, v_tail_4225_);
lean_closure_set(v___f_4246_, 3, v_params_4226_);
lean_closure_set(v___f_4246_, 4, v_is_4237_);
lean_closure_set(v___f_4246_, 5, v___x_4244_);
lean_closure_set(v___f_4246_, 6, v_head_4227_);
lean_closure_set(v___f_4246_, 7, v_ctors_4228_);
lean_closure_set(v___f_4246_, 8, v_numIndices_4229_);
lean_closure_set(v___f_4246_, 9, v___x_4230_);
lean_closure_set(v___f_4246_, 10, v___x_4231_);
lean_closure_set(v___f_4246_, 11, v_val_4232_);
lean_closure_set(v___f_4246_, 12, v_declName_4233_);
lean_closure_set(v___f_4246_, 13, v_levelParams_4234_);
lean_closure_set(v___f_4246_, 14, v_numParams_4235_);
lean_closure_set(v___f_4246_, 15, v___x_4236_);
lean_closure_set(v___f_4246_, 16, v_t_4238_);
lean_closure_set(v___f_4246_, 17, v___x_4245_);
v___x_4247_ = 0;
v___x_4248_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4238_, v___x_4245_, v___f_4246_, v___x_4247_, v___x_4247_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4249_ = _args[0];
lean_object* v_indName_4250_ = _args[1];
lean_object* v_tail_4251_ = _args[2];
lean_object* v_params_4252_ = _args[3];
lean_object* v_head_4253_ = _args[4];
lean_object* v_ctors_4254_ = _args[5];
lean_object* v_numIndices_4255_ = _args[6];
lean_object* v___x_4256_ = _args[7];
lean_object* v___x_4257_ = _args[8];
lean_object* v_val_4258_ = _args[9];
lean_object* v_declName_4259_ = _args[10];
lean_object* v_levelParams_4260_ = _args[11];
lean_object* v_numParams_4261_ = _args[12];
lean_object* v___x_4262_ = _args[13];
lean_object* v_is_4263_ = _args[14];
lean_object* v_t_4264_ = _args[15];
lean_object* v___y_4265_ = _args[16];
lean_object* v___y_4266_ = _args[17];
lean_object* v___y_4267_ = _args[18];
lean_object* v___y_4268_ = _args[19];
lean_object* v___y_4269_ = _args[20];
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4249_, v_indName_4250_, v_tail_4251_, v_params_4252_, v_head_4253_, v_ctors_4254_, v_numIndices_4255_, v___x_4256_, v___x_4257_, v_val_4258_, v_declName_4259_, v_levelParams_4260_, v_numParams_4261_, v___x_4262_, v_is_4263_, v_t_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4271_, lean_object* v_indName_4272_, lean_object* v_tail_4273_, lean_object* v_head_4274_, lean_object* v_ctors_4275_, lean_object* v_numIndices_4276_, lean_object* v___x_4277_, lean_object* v___x_4278_, lean_object* v_val_4279_, lean_object* v_declName_4280_, lean_object* v_levelParams_4281_, lean_object* v_numParams_4282_, lean_object* v_params_4283_, lean_object* v_t_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; lean_object* v___f_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4290_ = l_Lean_Expr_bindingBody_x21(v_t_4284_);
lean_inc_ref(v___x_4290_);
lean_inc(v_numIndices_4276_);
v___f_4291_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4291_, 0, v___x_4271_);
lean_closure_set(v___f_4291_, 1, v_indName_4272_);
lean_closure_set(v___f_4291_, 2, v_tail_4273_);
lean_closure_set(v___f_4291_, 3, v_params_4283_);
lean_closure_set(v___f_4291_, 4, v_head_4274_);
lean_closure_set(v___f_4291_, 5, v_ctors_4275_);
lean_closure_set(v___f_4291_, 6, v_numIndices_4276_);
lean_closure_set(v___f_4291_, 7, v___x_4277_);
lean_closure_set(v___f_4291_, 8, v___x_4278_);
lean_closure_set(v___f_4291_, 9, v_val_4279_);
lean_closure_set(v___f_4291_, 10, v_declName_4280_);
lean_closure_set(v___f_4291_, 11, v_levelParams_4281_);
lean_closure_set(v___f_4291_, 12, v_numParams_4282_);
lean_closure_set(v___f_4291_, 13, v___x_4290_);
v___x_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_numIndices_4276_);
v___x_4293_ = 0;
v___x_4294_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4290_, v___x_4292_, v___f_4291_, v___x_4293_, v___x_4293_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4295_ = _args[0];
lean_object* v_indName_4296_ = _args[1];
lean_object* v_tail_4297_ = _args[2];
lean_object* v_head_4298_ = _args[3];
lean_object* v_ctors_4299_ = _args[4];
lean_object* v_numIndices_4300_ = _args[5];
lean_object* v___x_4301_ = _args[6];
lean_object* v___x_4302_ = _args[7];
lean_object* v_val_4303_ = _args[8];
lean_object* v_declName_4304_ = _args[9];
lean_object* v_levelParams_4305_ = _args[10];
lean_object* v_numParams_4306_ = _args[11];
lean_object* v_params_4307_ = _args[12];
lean_object* v_t_4308_ = _args[13];
lean_object* v___y_4309_ = _args[14];
lean_object* v___y_4310_ = _args[15];
lean_object* v___y_4311_ = _args[16];
lean_object* v___y_4312_ = _args[17];
lean_object* v___y_4313_ = _args[18];
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4295_, v_indName_4296_, v_tail_4297_, v_head_4298_, v_ctors_4299_, v_numIndices_4300_, v___x_4301_, v___x_4302_, v_val_4303_, v_declName_4304_, v_levelParams_4305_, v_numParams_4306_, v_params_4307_, v_t_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v_t_4308_);
return v_res_4314_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4319_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4320_ = lean_unsigned_to_nat(58u);
v___x_4321_ = lean_unsigned_to_nat(142u);
v___x_4322_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4323_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4324_ = l_mkPanicMessageWithDecl(v___x_4323_, v___x_4322_, v___x_4321_, v___x_4320_, v___x_4319_);
return v___x_4324_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4325_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4326_ = lean_unsigned_to_nat(60u);
v___x_4327_ = lean_unsigned_to_nat(136u);
v___x_4328_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4329_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4330_ = l_mkPanicMessageWithDecl(v___x_4329_, v___x_4328_, v___x_4327_, v___x_4326_, v___x_4325_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4331_, lean_object* v_indName_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v___x_4338_; 
lean_inc(v_indName_4332_);
v___x_4338_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref(v___x_4338_);
if (lean_obj_tag(v_a_4339_) == 5)
{
lean_object* v_val_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v_val_4340_ = lean_ctor_get(v_a_4339_, 0);
lean_inc_ref(v_val_4340_);
lean_dec_ref(v_a_4339_);
v___x_4341_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4331_);
v___x_4342_ = l_Lean_Name_append(v_declName_4331_, v___x_4341_);
lean_inc(v_indName_4332_);
lean_inc(v___x_4342_);
v___x_4343_ = l_Lean_mkCasesOnSameCtorHet(v___x_4342_, v_indName_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4376_; 
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4376_ == 0)
{
lean_object* v_unused_4377_; 
v_unused_4377_ = lean_ctor_get(v___x_4343_, 0);
lean_dec(v_unused_4377_);
v___x_4345_ = v___x_4343_;
v_isShared_4346_ = v_isSharedCheck_4376_;
goto v_resetjp_4344_;
}
else
{
lean_dec(v___x_4343_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4376_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
lean_inc(v_indName_4332_);
v___x_4347_ = l_Lean_mkCasesOnName(v_indName_4332_);
v___x_4348_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4347_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v_levelParams_4350_; lean_object* v_type_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref(v___x_4348_);
v_levelParams_4350_ = lean_ctor_get(v_a_4349_, 1);
lean_inc_n(v_levelParams_4350_, 2);
v_type_4351_ = lean_ctor_get(v_a_4349_, 2);
lean_inc_ref(v_type_4351_);
lean_dec(v_a_4349_);
v___x_4352_ = lean_box(0);
v___x_4353_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4350_, v___x_4352_);
if (lean_obj_tag(v___x_4353_) == 1)
{
lean_object* v_head_4354_; lean_object* v_tail_4355_; lean_object* v_numParams_4356_; lean_object* v_numIndices_4357_; lean_object* v_ctors_4358_; lean_object* v___x_4359_; lean_object* v___f_4360_; lean_object* v___x_4362_; 
v_head_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_head_4354_);
v_tail_4355_ = lean_ctor_get(v___x_4353_, 1);
lean_inc(v_tail_4355_);
v_numParams_4356_ = lean_ctor_get(v_val_4340_, 1);
lean_inc_n(v_numParams_4356_, 2);
v_numIndices_4357_ = lean_ctor_get(v_val_4340_, 2);
lean_inc(v_numIndices_4357_);
v_ctors_4358_ = lean_ctor_get(v_val_4340_, 4);
lean_inc(v_ctors_4358_);
v___x_4359_ = l_Lean_instInhabitedExpr;
v___f_4360_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4360_, 0, v___x_4359_);
lean_closure_set(v___f_4360_, 1, v_indName_4332_);
lean_closure_set(v___f_4360_, 2, v_tail_4355_);
lean_closure_set(v___f_4360_, 3, v_head_4354_);
lean_closure_set(v___f_4360_, 4, v_ctors_4358_);
lean_closure_set(v___f_4360_, 5, v_numIndices_4357_);
lean_closure_set(v___f_4360_, 6, v___x_4342_);
lean_closure_set(v___f_4360_, 7, v___x_4353_);
lean_closure_set(v___f_4360_, 8, v_val_4340_);
lean_closure_set(v___f_4360_, 9, v_declName_4331_);
lean_closure_set(v___f_4360_, 10, v_levelParams_4350_);
lean_closure_set(v___f_4360_, 11, v_numParams_4356_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set_tag(v___x_4345_, 1);
lean_ctor_set(v___x_4345_, 0, v_numParams_4356_);
v___x_4362_ = v___x_4345_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_numParams_4356_);
v___x_4362_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
uint8_t v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = 0;
v___x_4364_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4351_, v___x_4362_, v___f_4360_, v___x_4363_, v___x_4363_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4364_;
}
}
else
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
lean_dec(v___x_4353_);
lean_dec_ref(v_type_4351_);
lean_dec(v_levelParams_4350_);
lean_del_object(v___x_4345_);
lean_dec(v___x_4342_);
lean_dec_ref(v_val_4340_);
lean_dec(v_indName_4332_);
lean_dec(v_declName_4331_);
v___x_4366_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4367_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4366_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4367_;
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_del_object(v___x_4345_);
lean_dec(v___x_4342_);
lean_dec_ref(v_val_4340_);
lean_dec(v_indName_4332_);
lean_dec(v_declName_4331_);
v_a_4368_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4348_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4348_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
}
else
{
lean_dec(v___x_4342_);
lean_dec_ref(v_val_4340_);
lean_dec(v_indName_4332_);
lean_dec(v_declName_4331_);
return v___x_4343_;
}
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_dec(v_a_4339_);
lean_dec(v_indName_4332_);
lean_dec(v_declName_4331_);
v___x_4378_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4379_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4378_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4379_;
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_indName_4332_);
lean_dec(v_declName_4331_);
v_a_4380_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4338_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4338_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4388_, lean_object* v_indName_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_mkCasesOnSameCtor(v_declName_4388_, v_indName_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4396_, lean_object* v_params_4397_, lean_object* v_motive_4398_, lean_object* v_as_4399_, lean_object* v_i_4400_, lean_object* v_j_4401_, lean_object* v_inv_4402_, lean_object* v_bs_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4396_, v_params_4397_, v_motive_4398_, v_as_4399_, v_i_4400_, v_j_4401_, v_bs_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4410_, lean_object* v_params_4411_, lean_object* v_motive_4412_, lean_object* v_as_4413_, lean_object* v_i_4414_, lean_object* v_j_4415_, lean_object* v_inv_4416_, lean_object* v_bs_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4410_, v_params_4411_, v_motive_4412_, v_as_4413_, v_i_4414_, v_j_4415_, v_inv_4416_, v_bs_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec_ref(v_as_4413_);
lean_dec_ref(v_params_4411_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4424_, lean_object* v_params_4425_, lean_object* v_a_4426_, lean_object* v_snd_4427_, lean_object* v_alts_4428_, lean_object* v_as_4429_, lean_object* v_i_4430_, lean_object* v_j_4431_, lean_object* v_inv_4432_, lean_object* v_bs_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4424_, v_params_4425_, v_a_4426_, v_snd_4427_, v_alts_4428_, v_as_4429_, v_i_4430_, v_j_4431_, v_bs_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4440_, lean_object* v_params_4441_, lean_object* v_a_4442_, lean_object* v_snd_4443_, lean_object* v_alts_4444_, lean_object* v_as_4445_, lean_object* v_i_4446_, lean_object* v_j_4447_, lean_object* v_inv_4448_, lean_object* v_bs_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4440_, v_params_4441_, v_a_4442_, v_snd_4443_, v_alts_4444_, v_as_4445_, v_i_4446_, v_j_4447_, v_inv_4448_, v_bs_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec_ref(v_as_4445_);
lean_dec_ref(v_params_4441_);
return v_res_4455_;
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
