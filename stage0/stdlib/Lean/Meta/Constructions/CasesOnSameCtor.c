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
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_auxDeclNGen_291_; lean_object* v_traceState_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v_newDecls_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_321_; 
v___x_287_ = lean_st_ref_take(v___y_280_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_289_ = lean_ctor_get(v___x_287_, 1);
v_ngen_290_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_291_ = lean_ctor_get(v___x_287_, 3);
v_traceState_292_ = lean_ctor_get(v___x_287_, 4);
v_messages_293_ = lean_ctor_get(v___x_287_, 6);
v_infoState_294_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_295_ = lean_ctor_get(v___x_287_, 8);
v_newDecls_296_ = lean_ctor_get(v___x_287_, 9);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_287_, 5);
lean_dec(v_unused_322_);
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_321_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_newDecls_296_);
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_321_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Environment_setExporting(v_env_288_, v_isExporting_281_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 5, v___x_282_);
lean_ctor_set(v___x_298_, 0, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_auxDeclNGen_291_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_320_, 5, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_320_, 6, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_320_, 7, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_320_, 8, v_snapshotTasks_295_);
lean_ctor_set(v_reuseFailAlloc_320_, 9, v_newDecls_296_);
v___x_302_ = v_reuseFailAlloc_320_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_mctx_305_; lean_object* v_zetaDeltaFVarIds_306_; lean_object* v_postponed_307_; lean_object* v_diag_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v___x_303_ = lean_st_ref_set(v___y_280_, v___x_302_);
v___x_304_ = lean_st_ref_take(v___y_283_);
v_mctx_305_ = lean_ctor_get(v___x_304_, 0);
v_zetaDeltaFVarIds_306_ = lean_ctor_get(v___x_304_, 2);
v_postponed_307_ = lean_ctor_get(v___x_304_, 3);
v_diag_308_ = lean_ctor_get(v___x_304_, 4);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v___x_304_, 1);
lean_dec(v_unused_319_);
v___x_310_ = v___x_304_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_diag_308_);
lean_inc(v_postponed_307_);
lean_inc(v_zetaDeltaFVarIds_306_);
lean_inc(v_mctx_305_);
lean_dec(v___x_304_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_284_);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_mctx_305_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_zetaDeltaFVarIds_306_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_postponed_307_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_diag_308_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_st_ref_set(v___y_283_, v___x_313_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_323_, lean_object* v_isExporting_324_, lean_object* v___x_325_, lean_object* v___y_326_, lean_object* v___x_327_, lean_object* v_a_x3f_328_, lean_object* v___y_329_){
_start:
{
uint8_t v_isExporting_boxed_330_; lean_object* v_res_331_; 
v_isExporting_boxed_330_ = lean_unbox(v_isExporting_324_);
v_res_331_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_323_, v_isExporting_boxed_330_, v___x_325_, v___y_326_, v___x_327_, v_a_x3f_328_);
lean_dec(v_a_x3f_328_);
lean_dec(v___y_326_);
lean_dec(v___y_323_);
return v_res_331_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_332_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_337_);
lean_ctor_set(v___x_338_, 5, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_339_, uint8_t v_isExporting_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_env_347_; uint8_t v_isExporting_348_; lean_object* v___x_349_; lean_object* v_env_350_; lean_object* v_nextMacroScope_351_; lean_object* v_ngen_352_; lean_object* v_auxDeclNGen_353_; lean_object* v_traceState_354_; lean_object* v_messages_355_; lean_object* v_infoState_356_; lean_object* v_snapshotTasks_357_; lean_object* v_newDecls_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_412_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v_isExporting_348_ = lean_ctor_get_uint8(v_env_347_, sizeof(void*)*8);
lean_dec_ref(v_env_347_);
v___x_349_ = lean_st_ref_take(v___y_344_);
v_env_350_ = lean_ctor_get(v___x_349_, 0);
v_nextMacroScope_351_ = lean_ctor_get(v___x_349_, 1);
v_ngen_352_ = lean_ctor_get(v___x_349_, 2);
v_auxDeclNGen_353_ = lean_ctor_get(v___x_349_, 3);
v_traceState_354_ = lean_ctor_get(v___x_349_, 4);
v_messages_355_ = lean_ctor_get(v___x_349_, 6);
v_infoState_356_ = lean_ctor_get(v___x_349_, 7);
v_snapshotTasks_357_ = lean_ctor_get(v___x_349_, 8);
v_newDecls_358_ = lean_ctor_get(v___x_349_, 9);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_349_, 5);
lean_dec(v_unused_413_);
v___x_360_ = v___x_349_;
v_isShared_361_ = v_isSharedCheck_412_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_newDecls_358_);
lean_inc(v_snapshotTasks_357_);
lean_inc(v_infoState_356_);
lean_inc(v_messages_355_);
lean_inc(v_traceState_354_);
lean_inc(v_auxDeclNGen_353_);
lean_inc(v_ngen_352_);
lean_inc(v_nextMacroScope_351_);
lean_inc(v_env_350_);
lean_dec(v___x_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_412_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_362_ = l_Lean_Environment_setExporting(v_env_350_, v_isExporting_340_);
v___x_363_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 5, v___x_363_);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_351_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_352_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_353_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_traceState_354_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_messages_355_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_infoState_356_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_snapshotTasks_357_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_newDecls_358_);
v___x_365_ = v_reuseFailAlloc_411_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_mctx_368_; lean_object* v_zetaDeltaFVarIds_369_; lean_object* v_postponed_370_; lean_object* v_diag_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_409_; 
v___x_366_ = lean_st_ref_set(v___y_344_, v___x_365_);
v___x_367_ = lean_st_ref_take(v___y_342_);
v_mctx_368_ = lean_ctor_get(v___x_367_, 0);
v_zetaDeltaFVarIds_369_ = lean_ctor_get(v___x_367_, 2);
v_postponed_370_ = lean_ctor_get(v___x_367_, 3);
v_diag_371_ = lean_ctor_get(v___x_367_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_367_, 1);
lean_dec(v_unused_410_);
v___x_373_ = v___x_367_;
v_isShared_374_ = v_isSharedCheck_409_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_diag_371_);
lean_inc(v_postponed_370_);
lean_inc(v_zetaDeltaFVarIds_369_);
lean_inc(v_mctx_368_);
lean_dec(v___x_367_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_409_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 1, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_mctx_368_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_369_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_370_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_371_);
v___x_377_ = v_reuseFailAlloc_408_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v_r_379_; 
v___x_378_ = lean_st_ref_set(v___y_342_, v___x_377_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
v_r_379_ = lean_apply_5(v_x_339_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, lean_box(0));
if (lean_obj_tag(v_r_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_396_; 
v_a_380_ = lean_ctor_get(v_r_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_r_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_382_ = v_r_379_;
v_isShared_383_ = v_isSharedCheck_396_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v_r_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_396_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
lean_inc(v_a_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 1);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_395_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v___x_386_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_344_, v_isExporting_348_, v___x_363_, v___y_342_, v___x_375_, v___x_385_);
lean_dec_ref(v___x_385_);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_394_);
v___x_388_ = v___x_386_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_dec(v___x_386_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_a_380_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_380_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_397_ = lean_ctor_get(v_r_379_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v_r_379_);
v___x_398_ = lean_box(0);
v___x_399_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_344_, v_isExporting_348_, v___x_363_, v___y_342_, v___x_375_, v___x_398_);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_399_, 0);
lean_dec(v_unused_407_);
v___x_401_ = v___x_399_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_399_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 1);
lean_ctor_set(v___x_401_, 0, v_a_397_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_397_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_414_, lean_object* v_isExporting_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v_isExporting_boxed_421_; lean_object* v_res_422_; 
v_isExporting_boxed_421_ = lean_unbox(v_isExporting_415_);
v_res_422_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_414_, v_isExporting_boxed_421_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_423_, lean_object* v_x_424_, uint8_t v_isExporting_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_424_, v_isExporting_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_432_, lean_object* v_x_433_, lean_object* v_isExporting_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
uint8_t v_isExporting_boxed_440_; lean_object* v_res_441_; 
v_isExporting_boxed_440_ = lean_unbox(v_isExporting_434_);
v_res_441_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_432_, v_x_433_, v_isExporting_boxed_440_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___f_449_; lean_object* v___x_15793__overap_450_; lean_object* v___x_451_; 
v___f_449_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15793__overap_450_ = lean_panic_fn_borrowed(v___f_449_, v_msg_443_);
lean_inc(v___y_447_);
lean_inc_ref(v___y_446_);
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
v___x_451_ = lean_apply_5(v___x_15793__overap_450_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, lean_box(0));
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_459_, lean_object* v_type_460_, lean_object* v_k_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = 0;
v___x_468_ = 0;
v___x_469_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_459_, v___x_467_, v_type_460_, v_k_461_, v___x_468_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_470_, lean_object* v_type_471_, lean_object* v_k_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_470_, v_type_471_, v_k_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_479_, lean_object* v_alts_480_, lean_object* v_j_481_, lean_object* v_zs1_482_, uint8_t v_isZero_483_, uint8_t v___x_484_, uint8_t v___x_485_, lean_object* v_zs2_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_array_get_borrowed(v___x_479_, v_alts_480_, v_j_481_);
v___x_494_ = l_Array_append___redArg(v_zs1_482_, v_zs2_486_);
lean_inc(v___x_493_);
v___x_495_ = l_Lean_mkAppN(v___x_493_, v___x_494_);
lean_dec_ref(v___x_494_);
v___x_496_ = l_Lean_Meta_mkLambdaFVars(v_zs2_486_, v___x_495_, v_isZero_483_, v___x_484_, v_isZero_483_, v___x_484_, v___x_485_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_497_, lean_object* v_alts_498_, lean_object* v_j_499_, lean_object* v_zs1_500_, lean_object* v_isZero_501_, lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v_zs2_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v_isZero_boxed_511_; uint8_t v___x_20888__boxed_512_; uint8_t v___x_20889__boxed_513_; lean_object* v_res_514_; 
v_isZero_boxed_511_ = lean_unbox(v_isZero_501_);
v___x_20888__boxed_512_ = lean_unbox(v___x_502_);
v___x_20889__boxed_513_ = lean_unbox(v___x_503_);
v_res_514_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_497_, v_alts_498_, v_j_499_, v_zs1_500_, v_isZero_boxed_511_, v___x_20888__boxed_512_, v___x_20889__boxed_513_, v_zs2_504_, v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_x_505_);
lean_dec_ref(v_zs2_504_);
lean_dec(v_j_499_);
lean_dec_ref(v_alts_498_);
lean_dec_ref(v___x_497_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_515_, lean_object* v_ism2_516_, lean_object* v_motive_517_, uint8_t v_isZero_518_, uint8_t v___x_519_, uint8_t v___x_520_, lean_object* v_a_521_, lean_object* v___f_522_, lean_object* v_zs1_523_, lean_object* v_val_524_, lean_object* v___x_525_, lean_object* v_indName_526_, lean_object* v___x_527_, lean_object* v___x_528_, lean_object* v_params_529_, lean_object* v___x_530_, lean_object* v_h_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = l_Array_append___redArg(v___x_515_, v_ism2_516_);
v___x_538_ = l_Lean_mkAppN(v_motive_517_, v___x_537_);
lean_dec_ref(v___x_537_);
v___x_539_ = l_Lean_Meta_mkLambdaFVars(v_ism2_516_, v___x_538_, v_isZero_518_, v___x_519_, v_isZero_518_, v___x_519_, v___x_520_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
v___x_541_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_521_, v___f_522_, v_isZero_518_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___y_544_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_541_);
v___x_547_ = l_Lean_InductiveVal_numCtors(v_val_524_);
v___x_548_ = lean_nat_dec_eq(v___x_547_, v___x_525_);
lean_dec(v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_530_);
v___x_549_ = l_Lean_mkConstructorElimName(v_indName_526_, v___x_527_);
v___x_550_ = l_Lean_mkConst(v___x_549_, v___x_528_);
v___x_551_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_552_ = lean_array_push(v___x_551_, v_a_540_);
v___x_553_ = l_Array_append___redArg(v_params_529_, v___x_552_);
lean_dec_ref(v___x_552_);
v___x_554_ = l_Array_append___redArg(v___x_553_, v_ism2_516_);
v___x_555_ = lean_unsigned_to_nat(2u);
v___x_556_ = lean_mk_empty_array_with_capacity(v___x_555_);
lean_inc_ref(v_h_531_);
v___x_557_ = lean_array_push(v___x_556_, v_h_531_);
v___x_558_ = lean_array_push(v___x_557_, v_a_542_);
v___x_559_ = l_Array_append___redArg(v___x_554_, v___x_558_);
lean_dec_ref(v___x_558_);
v___x_560_ = l_Lean_mkAppN(v___x_550_, v___x_559_);
lean_dec_ref(v___x_559_);
v___y_544_ = v___x_560_;
goto v___jp_543_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_527_);
lean_dec(v_indName_526_);
v___x_561_ = l_Lean_mkConst(v___x_530_, v___x_528_);
v___x_562_ = lean_mk_empty_array_with_capacity(v___x_525_);
lean_inc_ref(v___x_562_);
v___x_563_ = lean_array_push(v___x_562_, v_a_540_);
v___x_564_ = l_Array_append___redArg(v_params_529_, v___x_563_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_Array_append___redArg(v___x_564_, v_ism2_516_);
v___x_566_ = lean_array_push(v___x_562_, v_a_542_);
v___x_567_ = l_Array_append___redArg(v___x_565_, v___x_566_);
lean_dec_ref(v___x_566_);
v___x_568_ = l_Lean_mkAppN(v___x_561_, v___x_567_);
lean_dec_ref(v___x_567_);
v___y_544_ = v___x_568_;
goto v___jp_543_;
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_array_push(v_zs1_523_, v_h_531_);
v___x_546_ = l_Lean_Meta_mkLambdaFVars(v___x_545_, v___y_544_, v_isZero_518_, v___x_519_, v_isZero_518_, v___x_519_, v___x_520_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec_ref(v___x_545_);
return v___x_546_;
}
}
else
{
lean_dec(v_a_540_);
lean_dec_ref(v_h_531_);
lean_dec(v___x_530_);
lean_dec_ref(v_params_529_);
lean_dec(v___x_528_);
lean_dec(v___x_527_);
lean_dec(v_indName_526_);
lean_dec_ref(v_zs1_523_);
return v___x_541_;
}
}
else
{
lean_dec_ref(v_h_531_);
lean_dec(v___x_530_);
lean_dec_ref(v_params_529_);
lean_dec(v___x_528_);
lean_dec(v___x_527_);
lean_dec(v_indName_526_);
lean_dec_ref(v_zs1_523_);
lean_dec_ref(v___f_522_);
lean_dec_ref(v_a_521_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_569_ = _args[0];
lean_object* v_ism2_570_ = _args[1];
lean_object* v_motive_571_ = _args[2];
lean_object* v_isZero_572_ = _args[3];
lean_object* v___x_573_ = _args[4];
lean_object* v___x_574_ = _args[5];
lean_object* v_a_575_ = _args[6];
lean_object* v___f_576_ = _args[7];
lean_object* v_zs1_577_ = _args[8];
lean_object* v_val_578_ = _args[9];
lean_object* v___x_579_ = _args[10];
lean_object* v_indName_580_ = _args[11];
lean_object* v___x_581_ = _args[12];
lean_object* v___x_582_ = _args[13];
lean_object* v_params_583_ = _args[14];
lean_object* v___x_584_ = _args[15];
lean_object* v_h_585_ = _args[16];
lean_object* v___y_586_ = _args[17];
lean_object* v___y_587_ = _args[18];
lean_object* v___y_588_ = _args[19];
lean_object* v___y_589_ = _args[20];
lean_object* v___y_590_ = _args[21];
_start:
{
uint8_t v_isZero_boxed_591_; uint8_t v___x_20923__boxed_592_; uint8_t v___x_20924__boxed_593_; lean_object* v_res_594_; 
v_isZero_boxed_591_ = lean_unbox(v_isZero_572_);
v___x_20923__boxed_592_ = lean_unbox(v___x_573_);
v___x_20924__boxed_593_ = lean_unbox(v___x_574_);
v_res_594_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_569_, v_ism2_570_, v_motive_571_, v_isZero_boxed_591_, v___x_20923__boxed_592_, v___x_20924__boxed_593_, v_a_575_, v___f_576_, v_zs1_577_, v_val_578_, v___x_579_, v_indName_580_, v___x_581_, v___x_582_, v_params_583_, v___x_584_, v_h_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___x_579_);
lean_dec_ref(v_val_578_);
lean_dec_ref(v_ism2_570_);
return v_res_594_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v_dummy_596_; 
v___x_595_ = lean_box(0);
v_dummy_596_ = l_Lean_Expr_sort___override(v___x_595_);
return v_dummy_596_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_box(0);
v___x_604_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_605_ = l_Lean_mkConst(v___x_604_, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_606_, lean_object* v_alts_607_, lean_object* v_j_608_, uint8_t v_isZero_609_, uint8_t v___x_610_, uint8_t v___x_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_ism2_615_, lean_object* v_motive_616_, lean_object* v_a_617_, lean_object* v_val_618_, lean_object* v_indName_619_, lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v_params_622_, lean_object* v___x_623_, lean_object* v___x_624_, lean_object* v___x_625_, lean_object* v_zs1_626_, lean_object* v_ctorRet1_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
v___x_633_ = lean_whnf(v_ctorRet1_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v_dummy_640_; lean_object* v_nargs_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_box(v_isZero_609_);
v___x_636_ = lean_box(v___x_610_);
v___x_637_ = lean_box(v___x_611_);
lean_inc_ref(v_zs1_626_);
lean_inc(v_j_608_);
v___f_638_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_638_, 0, v___x_606_);
lean_closure_set(v___f_638_, 1, v_alts_607_);
lean_closure_set(v___f_638_, 2, v_j_608_);
lean_closure_set(v___f_638_, 3, v_zs1_626_);
lean_closure_set(v___f_638_, 4, v___x_635_);
lean_closure_set(v___f_638_, 5, v___x_636_);
lean_closure_set(v___f_638_, 6, v___x_637_);
v___x_639_ = l_Lean_mkAppN(v___x_612_, v_zs1_626_);
v_dummy_640_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_641_ = l_Lean_Expr_getAppNumArgs(v_a_634_);
lean_inc(v_nargs_641_);
v___x_642_ = lean_mk_array(v_nargs_641_, v_dummy_640_);
v___x_643_ = lean_nat_sub(v_nargs_641_, v___x_613_);
lean_dec(v_nargs_641_);
v___x_644_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_634_, v___x_642_, v___x_643_);
v___x_645_ = lean_array_get_size(v___x_644_);
v___x_646_ = l_Array_toSubarray___redArg(v___x_644_, v___x_614_, v___x_645_);
v___x_647_ = l_Subarray_copy___redArg(v___x_646_);
v___x_648_ = lean_array_push(v___x_647_, v___x_639_);
v___x_649_ = lean_box(v_isZero_609_);
v___x_650_ = lean_box(v___x_610_);
v___x_651_ = lean_box(v___x_611_);
lean_inc(v___x_613_);
v___f_652_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_652_, 0, v___x_648_);
lean_closure_set(v___f_652_, 1, v_ism2_615_);
lean_closure_set(v___f_652_, 2, v_motive_616_);
lean_closure_set(v___f_652_, 3, v___x_649_);
lean_closure_set(v___f_652_, 4, v___x_650_);
lean_closure_set(v___f_652_, 5, v___x_651_);
lean_closure_set(v___f_652_, 6, v_a_617_);
lean_closure_set(v___f_652_, 7, v___f_638_);
lean_closure_set(v___f_652_, 8, v_zs1_626_);
lean_closure_set(v___f_652_, 9, v_val_618_);
lean_closure_set(v___f_652_, 10, v___x_613_);
lean_closure_set(v___f_652_, 11, v_indName_619_);
lean_closure_set(v___f_652_, 12, v___x_620_);
lean_closure_set(v___f_652_, 13, v___x_621_);
lean_closure_set(v___f_652_, 14, v_params_622_);
lean_closure_set(v___f_652_, 15, v___x_623_);
v___x_653_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_654_ = l_Lean_Level_ofNat(v___x_613_);
lean_dec(v___x_613_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_mkConst(v___x_653_, v___x_656_);
v___x_658_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_659_ = l_Lean_mkRawNatLit(v_j_608_);
v___x_660_ = l_Lean_mkApp3(v___x_657_, v___x_658_, v___x_624_, v___x_659_);
v___x_661_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_625_, v___x_660_, v___f_652_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_661_;
}
else
{
lean_dec_ref(v_zs1_626_);
lean_dec(v___x_625_);
lean_dec_ref(v___x_624_);
lean_dec(v___x_623_);
lean_dec_ref(v_params_622_);
lean_dec(v___x_621_);
lean_dec(v___x_620_);
lean_dec(v_indName_619_);
lean_dec_ref(v_val_618_);
lean_dec_ref(v_a_617_);
lean_dec_ref(v_motive_616_);
lean_dec_ref(v_ism2_615_);
lean_dec(v___x_614_);
lean_dec(v___x_613_);
lean_dec_ref(v___x_612_);
lean_dec(v_j_608_);
lean_dec_ref(v_alts_607_);
lean_dec_ref(v___x_606_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_662_ = _args[0];
lean_object* v_alts_663_ = _args[1];
lean_object* v_j_664_ = _args[2];
lean_object* v_isZero_665_ = _args[3];
lean_object* v___x_666_ = _args[4];
lean_object* v___x_667_ = _args[5];
lean_object* v___x_668_ = _args[6];
lean_object* v___x_669_ = _args[7];
lean_object* v___x_670_ = _args[8];
lean_object* v_ism2_671_ = _args[9];
lean_object* v_motive_672_ = _args[10];
lean_object* v_a_673_ = _args[11];
lean_object* v_val_674_ = _args[12];
lean_object* v_indName_675_ = _args[13];
lean_object* v___x_676_ = _args[14];
lean_object* v___x_677_ = _args[15];
lean_object* v_params_678_ = _args[16];
lean_object* v___x_679_ = _args[17];
lean_object* v___x_680_ = _args[18];
lean_object* v___x_681_ = _args[19];
lean_object* v_zs1_682_ = _args[20];
lean_object* v_ctorRet1_683_ = _args[21];
lean_object* v___y_684_ = _args[22];
lean_object* v___y_685_ = _args[23];
lean_object* v___y_686_ = _args[24];
lean_object* v___y_687_ = _args[25];
lean_object* v___y_688_ = _args[26];
_start:
{
uint8_t v_isZero_boxed_689_; uint8_t v___x_21054__boxed_690_; uint8_t v___x_21055__boxed_691_; lean_object* v_res_692_; 
v_isZero_boxed_689_ = lean_unbox(v_isZero_665_);
v___x_21054__boxed_690_ = lean_unbox(v___x_666_);
v___x_21055__boxed_691_ = lean_unbox(v___x_667_);
v_res_692_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_662_, v_alts_663_, v_j_664_, v_isZero_boxed_689_, v___x_21054__boxed_690_, v___x_21055__boxed_691_, v___x_668_, v___x_669_, v___x_670_, v_ism2_671_, v_motive_672_, v_a_673_, v_val_674_, v_indName_675_, v___x_676_, v___x_677_, v_params_678_, v___x_679_, v___x_680_, v___x_681_, v_zs1_682_, v_ctorRet1_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_696_, lean_object* v_params_697_, lean_object* v_alts_698_, lean_object* v___x_699_, lean_object* v_ism2_700_, lean_object* v_motive_701_, lean_object* v_val_702_, lean_object* v_indName_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_as_707_, lean_object* v_i_708_, lean_object* v_j_709_, lean_object* v_bs_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_zero_716_; uint8_t v_isZero_717_; 
v_zero_716_ = lean_unsigned_to_nat(0u);
v_isZero_717_ = lean_nat_dec_eq(v_i_708_, v_zero_716_);
if (v_isZero_717_ == 1)
{
lean_object* v___x_718_; 
lean_dec(v_j_709_);
lean_dec(v_i_708_);
lean_dec_ref(v___x_706_);
lean_dec(v___x_705_);
lean_dec(v___x_704_);
lean_dec(v_indName_703_);
lean_dec_ref(v_val_702_);
lean_dec_ref(v_motive_701_);
lean_dec_ref(v_ism2_700_);
lean_dec(v___x_699_);
lean_dec_ref(v_alts_698_);
lean_dec_ref(v_params_697_);
lean_dec(v_tail_696_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_bs_710_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v_n_720_; lean_object* v___y_722_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v_n_720_ = lean_nat_sub(v_i_708_, v___x_719_);
lean_dec(v_i_708_);
v___x_735_ = lean_array_fget_borrowed(v_as_707_, v_j_709_);
lean_inc(v_tail_696_);
lean_inc(v___x_735_);
v___x_736_ = l_Lean_mkConst(v___x_735_, v_tail_696_);
v___x_737_ = l_Lean_mkAppN(v___x_736_, v_params_697_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc_ref(v___x_737_);
v___x_738_ = lean_infer_type(v___x_737_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_n(v_a_739_, 2);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_instInhabitedExpr;
v___x_741_ = 1;
v___x_742_ = 1;
v___x_743_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_744_ = lean_box(v_isZero_717_);
v___x_745_ = lean_box(v___x_741_);
v___x_746_ = lean_box(v___x_742_);
lean_inc_ref(v___x_706_);
lean_inc(v___x_705_);
lean_inc_ref(v_params_697_);
lean_inc(v___x_704_);
lean_inc(v___x_735_);
lean_inc(v_indName_703_);
lean_inc_ref(v_val_702_);
lean_inc_ref(v_motive_701_);
lean_inc_ref(v_ism2_700_);
lean_inc(v___x_699_);
lean_inc(v_j_709_);
lean_inc_ref(v_alts_698_);
v___f_747_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_747_, 0, v___x_740_);
lean_closure_set(v___f_747_, 1, v_alts_698_);
lean_closure_set(v___f_747_, 2, v_j_709_);
lean_closure_set(v___f_747_, 3, v___x_744_);
lean_closure_set(v___f_747_, 4, v___x_745_);
lean_closure_set(v___f_747_, 5, v___x_746_);
lean_closure_set(v___f_747_, 6, v___x_737_);
lean_closure_set(v___f_747_, 7, v___x_719_);
lean_closure_set(v___f_747_, 8, v___x_699_);
lean_closure_set(v___f_747_, 9, v_ism2_700_);
lean_closure_set(v___f_747_, 10, v_motive_701_);
lean_closure_set(v___f_747_, 11, v_a_739_);
lean_closure_set(v___f_747_, 12, v_val_702_);
lean_closure_set(v___f_747_, 13, v_indName_703_);
lean_closure_set(v___f_747_, 14, v___x_735_);
lean_closure_set(v___f_747_, 15, v___x_704_);
lean_closure_set(v___f_747_, 16, v_params_697_);
lean_closure_set(v___f_747_, 17, v___x_705_);
lean_closure_set(v___f_747_, 18, v___x_706_);
lean_closure_set(v___f_747_, 19, v___x_743_);
v___x_748_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_739_, v___f_747_, v_isZero_717_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
v___y_722_ = v___x_748_;
goto v___jp_721_;
}
else
{
lean_dec_ref(v___x_737_);
v___y_722_ = v___x_738_;
goto v___jp_721_;
}
v___jp_721_:
{
if (lean_obj_tag(v___y_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_723_ = lean_ctor_get(v___y_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___y_722_);
v___x_724_ = lean_nat_add(v_j_709_, v___x_719_);
lean_dec(v_j_709_);
v___x_725_ = lean_array_push(v_bs_710_, v_a_723_);
v_i_708_ = v_n_720_;
v_j_709_ = v___x_724_;
v_bs_710_ = v___x_725_;
goto _start;
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_n_720_);
lean_dec_ref(v_bs_710_);
lean_dec(v_j_709_);
lean_dec_ref(v___x_706_);
lean_dec(v___x_705_);
lean_dec(v___x_704_);
lean_dec(v_indName_703_);
lean_dec_ref(v_val_702_);
lean_dec_ref(v_motive_701_);
lean_dec_ref(v_ism2_700_);
lean_dec(v___x_699_);
lean_dec_ref(v_alts_698_);
lean_dec_ref(v_params_697_);
lean_dec(v_tail_696_);
v_a_727_ = lean_ctor_get(v___y_722_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___y_722_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___y_722_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___y_722_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_749_ = _args[0];
lean_object* v_params_750_ = _args[1];
lean_object* v_alts_751_ = _args[2];
lean_object* v___x_752_ = _args[3];
lean_object* v_ism2_753_ = _args[4];
lean_object* v_motive_754_ = _args[5];
lean_object* v_val_755_ = _args[6];
lean_object* v_indName_756_ = _args[7];
lean_object* v___x_757_ = _args[8];
lean_object* v___x_758_ = _args[9];
lean_object* v___x_759_ = _args[10];
lean_object* v_as_760_ = _args[11];
lean_object* v_i_761_ = _args[12];
lean_object* v_j_762_ = _args[13];
lean_object* v_bs_763_ = _args[14];
lean_object* v___y_764_ = _args[15];
lean_object* v___y_765_ = _args[16];
lean_object* v___y_766_ = _args[17];
lean_object* v___y_767_ = _args[18];
lean_object* v___y_768_ = _args[19];
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_749_, v_params_750_, v_alts_751_, v___x_752_, v_ism2_753_, v_motive_754_, v_val_755_, v_indName_756_, v___x_757_, v___x_758_, v___x_759_, v_as_760_, v_i_761_, v_j_762_, v_bs_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_as_760_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v_ism1_773_, uint8_t v___x_774_, uint8_t v___x_775_, uint8_t v___x_776_, lean_object* v___x_777_, lean_object* v_tail_778_, lean_object* v_params_779_, lean_object* v_alts_780_, lean_object* v_numParams_781_, lean_object* v_ism2_782_, lean_object* v_val_783_, lean_object* v_indName_784_, lean_object* v___x_785_, lean_object* v___x_786_, lean_object* v___x_787_, lean_object* v_name_788_, lean_object* v___x_789_, lean_object* v_heq_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc_ref(v_motive_770_);
v___x_796_ = l_Lean_mkAppN(v_motive_770_, v___x_771_);
v___x_797_ = l_Lean_mkArrow(v_a_772_, v___x_796_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = l_Lean_Meta_mkLambdaFVars(v_ism1_773_, v_a_798_, v___x_774_, v___x_775_, v___x_774_, v___x_775_, v___x_776_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = lean_array_get_size(v___x_777_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_mk_empty_array_with_capacity(v___x_801_);
lean_inc(v___x_785_);
lean_inc_ref(v_motive_770_);
lean_inc_ref(v_ism2_782_);
lean_inc_ref(v_alts_780_);
lean_inc_ref(v_params_779_);
v___x_804_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_778_, v_params_779_, v_alts_780_, v_numParams_781_, v_ism2_782_, v_motive_770_, v_val_783_, v_indName_784_, v___x_785_, v___x_786_, v___x_787_, v___x_777_, v___x_801_, v___x_802_, v___x_803_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_804_);
lean_inc_ref(v_heq_790_);
v___x_806_ = l_Lean_Meta_mkEqSymm(v_heq_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v___x_808_ = l_Lean_mkConst(v_name_788_, v___x_785_);
v___x_809_ = l_Lean_mkAppN(v___x_808_, v_params_779_);
v___x_810_ = l_Lean_Expr_app___override(v___x_809_, v_a_800_);
v___x_811_ = l_Lean_mkAppN(v___x_810_, v_ism1_773_);
v___x_812_ = l_Lean_mkAppN(v___x_811_, v_a_805_);
lean_dec(v_a_805_);
v___x_813_ = l_Lean_Expr_app___override(v___x_812_, v_a_807_);
v___x_814_ = lean_mk_empty_array_with_capacity(v___x_789_);
lean_inc_ref(v___x_814_);
v___x_815_ = lean_array_push(v___x_814_, v_motive_770_);
v___x_816_ = l_Array_append___redArg(v_params_779_, v___x_815_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_Array_append___redArg(v___x_816_, v_ism1_773_);
v___x_818_ = l_Array_append___redArg(v___x_817_, v_ism2_782_);
lean_dec_ref(v_ism2_782_);
v___x_819_ = lean_array_push(v___x_814_, v_heq_790_);
v___x_820_ = l_Array_append___redArg(v___x_818_, v___x_819_);
lean_dec_ref(v___x_819_);
v___x_821_ = l_Array_append___redArg(v___x_820_, v_alts_780_);
lean_dec_ref(v_alts_780_);
v___x_822_ = l_Lean_Meta_mkLambdaFVars(v___x_821_, v___x_813_, v___x_774_, v___x_775_, v___x_774_, v___x_775_, v___x_776_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec_ref(v___x_821_);
return v___x_822_;
}
else
{
lean_dec(v_a_805_);
lean_dec(v_a_800_);
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec(v___x_785_);
lean_dec_ref(v_ism2_782_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec_ref(v_motive_770_);
return v___x_806_;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_a_800_);
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec(v___x_785_);
lean_dec_ref(v_ism2_782_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec_ref(v_motive_770_);
v_a_823_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_804_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_804_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec_ref(v___x_787_);
lean_dec(v___x_786_);
lean_dec(v___x_785_);
lean_dec(v_indName_784_);
lean_dec_ref(v_val_783_);
lean_dec_ref(v_ism2_782_);
lean_dec(v_numParams_781_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec(v_tail_778_);
lean_dec_ref(v_motive_770_);
return v___x_799_;
}
}
else
{
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec_ref(v___x_787_);
lean_dec(v___x_786_);
lean_dec(v___x_785_);
lean_dec(v_indName_784_);
lean_dec_ref(v_val_783_);
lean_dec_ref(v_ism2_782_);
lean_dec(v_numParams_781_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec(v_tail_778_);
lean_dec_ref(v_motive_770_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_831_ = _args[0];
lean_object* v___x_832_ = _args[1];
lean_object* v_a_833_ = _args[2];
lean_object* v_ism1_834_ = _args[3];
lean_object* v___x_835_ = _args[4];
lean_object* v___x_836_ = _args[5];
lean_object* v___x_837_ = _args[6];
lean_object* v___x_838_ = _args[7];
lean_object* v_tail_839_ = _args[8];
lean_object* v_params_840_ = _args[9];
lean_object* v_alts_841_ = _args[10];
lean_object* v_numParams_842_ = _args[11];
lean_object* v_ism2_843_ = _args[12];
lean_object* v_val_844_ = _args[13];
lean_object* v_indName_845_ = _args[14];
lean_object* v___x_846_ = _args[15];
lean_object* v___x_847_ = _args[16];
lean_object* v___x_848_ = _args[17];
lean_object* v_name_849_ = _args[18];
lean_object* v___x_850_ = _args[19];
lean_object* v_heq_851_ = _args[20];
lean_object* v___y_852_ = _args[21];
lean_object* v___y_853_ = _args[22];
lean_object* v___y_854_ = _args[23];
lean_object* v___y_855_ = _args[24];
lean_object* v___y_856_ = _args[25];
_start:
{
uint8_t v___x_21279__boxed_857_; uint8_t v___x_21280__boxed_858_; uint8_t v___x_21281__boxed_859_; lean_object* v_res_860_; 
v___x_21279__boxed_857_ = lean_unbox(v___x_835_);
v___x_21280__boxed_858_ = lean_unbox(v___x_836_);
v___x_21281__boxed_859_ = lean_unbox(v___x_837_);
v_res_860_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_831_, v___x_832_, v_a_833_, v_ism1_834_, v___x_21279__boxed_857_, v___x_21280__boxed_858_, v___x_21281__boxed_859_, v___x_838_, v_tail_839_, v_params_840_, v_alts_841_, v_numParams_842_, v_ism2_843_, v_val_844_, v_indName_845_, v___x_846_, v___x_847_, v___x_848_, v_name_849_, v___x_850_, v_heq_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___x_850_);
lean_dec_ref(v___x_838_);
lean_dec_ref(v_ism1_834_);
lean_dec_ref(v___x_832_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_861_, lean_object* v_tail_862_, lean_object* v_params_863_, lean_object* v_ism1_864_, lean_object* v_ism2_865_, lean_object* v_motive_866_, lean_object* v___x_867_, uint8_t v___x_868_, uint8_t v___x_869_, uint8_t v___x_870_, lean_object* v___x_871_, lean_object* v_numParams_872_, lean_object* v_val_873_, lean_object* v___x_874_, lean_object* v___x_875_, lean_object* v_name_876_, lean_object* v___x_877_, lean_object* v_alts_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_inc(v_indName_861_);
v___x_884_ = l_mkCtorIdxName(v_indName_861_);
lean_inc(v_tail_862_);
v___x_885_ = l_Lean_mkConst(v___x_884_, v_tail_862_);
lean_inc_ref_n(v_params_863_, 2);
v___x_886_ = l_Array_append___redArg(v_params_863_, v_ism1_864_);
lean_inc_ref(v___x_885_);
v___x_887_ = l_Lean_mkAppN(v___x_885_, v___x_886_);
lean_dec_ref(v___x_886_);
v___x_888_ = l_Array_append___redArg(v_params_863_, v_ism2_865_);
v___x_889_ = l_Lean_mkAppN(v___x_885_, v___x_888_);
lean_dec_ref(v___x_888_);
lean_inc_ref(v___x_889_);
lean_inc_ref(v___x_887_);
v___x_890_ = l_Lean_Meta_mkEq(v___x_887_, v___x_889_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
lean_inc_ref(v___x_889_);
v___x_892_ = l_Lean_Meta_mkEq(v___x_889_, v___x_887_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___f_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_892_);
v___x_894_ = lean_box(v___x_868_);
v___x_895_ = lean_box(v___x_869_);
v___x_896_ = lean_box(v___x_870_);
v___f_897_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_897_, 0, v_motive_866_);
lean_closure_set(v___f_897_, 1, v___x_867_);
lean_closure_set(v___f_897_, 2, v_a_893_);
lean_closure_set(v___f_897_, 3, v_ism1_864_);
lean_closure_set(v___f_897_, 4, v___x_894_);
lean_closure_set(v___f_897_, 5, v___x_895_);
lean_closure_set(v___f_897_, 6, v___x_896_);
lean_closure_set(v___f_897_, 7, v___x_871_);
lean_closure_set(v___f_897_, 8, v_tail_862_);
lean_closure_set(v___f_897_, 9, v_params_863_);
lean_closure_set(v___f_897_, 10, v_alts_878_);
lean_closure_set(v___f_897_, 11, v_numParams_872_);
lean_closure_set(v___f_897_, 12, v_ism2_865_);
lean_closure_set(v___f_897_, 13, v_val_873_);
lean_closure_set(v___f_897_, 14, v_indName_861_);
lean_closure_set(v___f_897_, 15, v___x_874_);
lean_closure_set(v___f_897_, 16, v___x_875_);
lean_closure_set(v___f_897_, 17, v___x_889_);
lean_closure_set(v___f_897_, 18, v_name_876_);
lean_closure_set(v___f_897_, 19, v___x_877_);
v___x_898_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_899_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_898_, v_a_891_, v___f_897_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_899_;
}
else
{
lean_dec(v_a_891_);
lean_dec_ref(v___x_889_);
lean_dec_ref(v_alts_878_);
lean_dec(v___x_877_);
lean_dec(v_name_876_);
lean_dec(v___x_875_);
lean_dec(v___x_874_);
lean_dec_ref(v_val_873_);
lean_dec(v_numParams_872_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_867_);
lean_dec_ref(v_motive_866_);
lean_dec_ref(v_ism2_865_);
lean_dec_ref(v_ism1_864_);
lean_dec_ref(v_params_863_);
lean_dec(v_tail_862_);
lean_dec(v_indName_861_);
return v___x_892_;
}
}
else
{
lean_dec_ref(v___x_889_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v_alts_878_);
lean_dec(v___x_877_);
lean_dec(v_name_876_);
lean_dec(v___x_875_);
lean_dec(v___x_874_);
lean_dec_ref(v_val_873_);
lean_dec(v_numParams_872_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_867_);
lean_dec_ref(v_motive_866_);
lean_dec_ref(v_ism2_865_);
lean_dec_ref(v_ism1_864_);
lean_dec_ref(v_params_863_);
lean_dec(v_tail_862_);
lean_dec(v_indName_861_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_900_ = _args[0];
lean_object* v_tail_901_ = _args[1];
lean_object* v_params_902_ = _args[2];
lean_object* v_ism1_903_ = _args[3];
lean_object* v_ism2_904_ = _args[4];
lean_object* v_motive_905_ = _args[5];
lean_object* v___x_906_ = _args[6];
lean_object* v___x_907_ = _args[7];
lean_object* v___x_908_ = _args[8];
lean_object* v___x_909_ = _args[9];
lean_object* v___x_910_ = _args[10];
lean_object* v_numParams_911_ = _args[11];
lean_object* v_val_912_ = _args[12];
lean_object* v___x_913_ = _args[13];
lean_object* v___x_914_ = _args[14];
lean_object* v_name_915_ = _args[15];
lean_object* v___x_916_ = _args[16];
lean_object* v_alts_917_ = _args[17];
lean_object* v___y_918_ = _args[18];
lean_object* v___y_919_ = _args[19];
lean_object* v___y_920_ = _args[20];
lean_object* v___y_921_ = _args[21];
lean_object* v___y_922_ = _args[22];
_start:
{
uint8_t v___x_21406__boxed_923_; uint8_t v___x_21407__boxed_924_; uint8_t v___x_21408__boxed_925_; lean_object* v_res_926_; 
v___x_21406__boxed_923_ = lean_unbox(v___x_907_);
v___x_21407__boxed_924_ = lean_unbox(v___x_908_);
v___x_21408__boxed_925_ = lean_unbox(v___x_909_);
v_res_926_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_900_, v_tail_901_, v_params_902_, v_ism1_903_, v_ism2_904_, v_motive_905_, v___x_906_, v___x_21406__boxed_923_, v___x_21407__boxed_924_, v___x_21408__boxed_925_, v___x_910_, v_numParams_911_, v_val_912_, v___x_913_, v___x_914_, v_name_915_, v___x_916_, v_alts_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v_snd_927_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_935_, lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_935_, v_x_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_x_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_943_, size_t v_i_944_, lean_object* v_bs_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_946_ == 0)
{
return v_bs_945_;
}
else
{
lean_object* v_v_947_; lean_object* v_fst_948_; lean_object* v_snd_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_963_; 
v_v_947_ = lean_array_uget(v_bs_945_, v_i_944_);
v_fst_948_ = lean_ctor_get(v_v_947_, 0);
v_snd_949_ = lean_ctor_get(v_v_947_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_v_947_);
if (v_isSharedCheck_963_ == 0)
{
v___x_951_ = v_v_947_;
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_snd_949_);
lean_inc(v_fst_948_);
lean_dec(v_v_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v_bs_x27_954_; lean_object* v___f_955_; lean_object* v___x_957_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v_bs_x27_954_ = lean_array_uset(v_bs_945_, v_i_944_, v___x_953_);
v___f_955_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_955_, 0, v_snd_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___f_955_);
v___x_957_ = v___x_951_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_fst_948_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___f_955_);
v___x_957_ = v_reuseFailAlloc_962_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_944_, v___x_958_);
v___x_960_ = lean_array_uset(v_bs_x27_954_, v_i_944_, v___x_957_);
v_i_944_ = v___x_959_;
v_bs_945_ = v___x_960_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_964_, lean_object* v_i_965_, lean_object* v_bs_966_){
_start:
{
size_t v_sz_boxed_967_; size_t v_i_boxed_968_; lean_object* v_res_969_; 
v_sz_boxed_967_ = lean_unbox_usize(v_sz_964_);
lean_dec(v_sz_964_);
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_967_, v_i_boxed_968_, v_bs_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_970_, lean_object* v_a_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_20309__overap_978_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_instInhabitedExpr;
v___x_20309__overap_978_ = l_instInhabitedOfMonad___redArg(v___x_970_, v___x_977_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
v___x_979_ = lean_apply_5(v___x_20309__overap_978_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, lean_box(0));
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_980_, lean_object* v_a_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_980_, v_a_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_a_981_);
return v_res_987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_instMonadEIO(lean_box(0));
return v___x_988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_990_ = l_StateRefT_x27_instMonad___redArg(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_995_, lean_object* v_declInfos_996_, lean_object* v_k_997_, lean_object* v_kind_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v_kind_boxed_1005_; lean_object* v_res_1006_; 
v_kind_boxed_1005_ = lean_unbox(v_kind_998_);
v_res_1006_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_995_, v_declInfos_996_, v_k_997_, v_kind_boxed_1005_, v_x_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1007_, lean_object* v_k_1008_, uint8_t v_kind_1009_, lean_object* v_acc_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v_toApplicative_1017_; lean_object* v_toFunctor_1018_; lean_object* v_toSeq_1019_; lean_object* v_toSeqLeft_1020_; lean_object* v_toSeqRight_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_toApplicative_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1082_; 
v___x_1016_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1017_ = lean_ctor_get(v___x_1016_, 0);
v_toFunctor_1018_ = lean_ctor_get(v_toApplicative_1017_, 0);
v_toSeq_1019_ = lean_ctor_get(v_toApplicative_1017_, 2);
v_toSeqLeft_1020_ = lean_ctor_get(v_toApplicative_1017_, 3);
v_toSeqRight_1021_ = lean_ctor_get(v_toApplicative_1017_, 4);
v___f_1022_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1023_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1018_, 2);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toFunctor_1018_);
v___f_1025_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1025_, 0, v_toFunctor_1018_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___f_1024_);
lean_ctor_set(v___x_1026_, 1, v___f_1025_);
lean_inc(v_toSeqRight_1021_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toSeqRight_1021_);
lean_inc(v_toSeqLeft_1020_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toSeqLeft_1020_);
lean_inc(v_toSeq_1019_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toSeq_1019_);
v___x_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1026_);
lean_ctor_set(v___x_1030_, 1, v___f_1022_);
lean_ctor_set(v___x_1030_, 2, v___f_1029_);
lean_ctor_set(v___x_1030_, 3, v___f_1028_);
lean_ctor_set(v___x_1030_, 4, v___f_1027_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___f_1023_);
v___x_1032_ = l_StateRefT_x27_instMonad___redArg(v___x_1031_);
v_toApplicative_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1032_, 1);
lean_dec(v_unused_1083_);
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1082_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_toApplicative_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1082_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_toFunctor_1037_; lean_object* v_toSeq_1038_; lean_object* v_toSeqLeft_1039_; lean_object* v_toSeqRight_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1080_; 
v_toFunctor_1037_ = lean_ctor_get(v_toApplicative_1033_, 0);
v_toSeq_1038_ = lean_ctor_get(v_toApplicative_1033_, 2);
v_toSeqLeft_1039_ = lean_ctor_get(v_toApplicative_1033_, 3);
v_toSeqRight_1040_ = lean_ctor_get(v_toApplicative_1033_, 4);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_toApplicative_1033_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_toApplicative_1033_, 1);
lean_dec(v_unused_1081_);
v___x_1042_ = v_toApplicative_1033_;
v_isShared_1043_ = v_isSharedCheck_1080_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_toSeqRight_1040_);
lean_inc(v_toSeqLeft_1039_);
lean_inc(v_toSeq_1038_);
lean_inc(v_toFunctor_1037_);
lean_dec(v_toApplicative_1033_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1080_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1053_; 
v___f_1044_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1045_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1037_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toFunctor_1037_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toFunctor_1037_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___f_1046_);
lean_ctor_set(v___x_1048_, 1, v___f_1047_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeqRight_1040_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toSeqLeft_1039_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toSeq_1038_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___f_1049_);
lean_ctor_set(v___x_1042_, 3, v___f_1050_);
lean_ctor_set(v___x_1042_, 2, v___f_1051_);
lean_ctor_set(v___x_1042_, 1, v___f_1044_);
lean_ctor_set(v___x_1042_, 0, v___x_1048_);
v___x_1053_ = v___x_1042_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___f_1044_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___f_1051_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___f_1049_);
v___x_1053_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___f_1045_);
lean_ctor_set(v___x_1035_, 0, v___x_1053_);
v___x_1055_ = v___x_1035_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___f_1045_);
v___x_1055_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = lean_array_get_size(v_acc_1010_);
v___x_1057_ = lean_array_get_size(v_declInfos_1007_);
v___x_1058_ = lean_nat_dec_lt(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_declInfos_1007_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
v___x_1059_ = lean_apply_6(v_k_1008_, v_acc_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, lean_box(0));
return v___x_1059_;
}
else
{
lean_object* v___f_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_snd_1068_; lean_object* v_fst_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; lean_object* v___x_1072_; 
v___f_1060_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1060_, 0, v___x_1055_);
v___x_1061_ = lean_box(0);
v___x_1062_ = 0;
v___f_1063_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1063_, 0, v___f_1060_);
v___x_1064_ = lean_box(v___x_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___f_1063_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1061_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_array_get(v___x_1066_, v_declInfos_1007_, v___x_1056_);
lean_dec_ref(v___x_1066_);
v_snd_1068_ = lean_ctor_get(v___x_1067_, 1);
lean_inc(v_snd_1068_);
v_fst_1069_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_fst_1069_);
lean_dec(v___x_1067_);
v_fst_1070_ = lean_ctor_get(v_snd_1068_, 0);
lean_inc(v_fst_1070_);
v_snd_1071_ = lean_ctor_get(v_snd_1068_, 1);
lean_inc(v_snd_1071_);
lean_dec(v_snd_1068_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc_ref(v_acc_1010_);
v___x_1072_ = lean_apply_6(v_snd_1071_, v_acc_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, lean_box(0));
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___f_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = lean_box(v_kind_1009_);
v___f_1075_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1075_, 0, v_acc_1010_);
lean_closure_set(v___f_1075_, 1, v_declInfos_1007_);
lean_closure_set(v___f_1075_, 2, v_k_1008_);
lean_closure_set(v___f_1075_, 3, v___x_1074_);
v___x_1076_ = lean_unbox(v_fst_1070_);
lean_dec(v_fst_1070_);
v___x_1077_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1069_, v___x_1076_, v_a_1073_, v___f_1075_, v_kind_1009_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1077_;
}
else
{
lean_dec(v_fst_1070_);
lean_dec(v_fst_1069_);
lean_dec_ref(v_acc_1010_);
lean_dec_ref(v_k_1008_);
lean_dec_ref(v_declInfos_1007_);
return v___x_1072_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1084_, lean_object* v_declInfos_1085_, lean_object* v_k_1086_, uint8_t v_kind_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_array_push(v_acc_1084_, v_x_1088_);
v___x_1095_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1085_, v_k_1086_, v_kind_1087_, v___x_1094_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1096_, lean_object* v_k_1097_, lean_object* v_kind_1098_, lean_object* v_acc_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v_kind_boxed_1105_; lean_object* v_res_1106_; 
v_kind_boxed_1105_ = lean_unbox(v_kind_1098_);
v_res_1106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1096_, v_k_1097_, v_kind_boxed_1105_, v_acc_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1109_, lean_object* v_k_1110_, uint8_t v_kind_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1118_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1109_, v_k_1110_, v_kind_1111_, v___x_1117_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1119_, lean_object* v_k_1120_, lean_object* v_kind_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v_kind_boxed_1127_; lean_object* v_res_1128_; 
v_kind_boxed_1127_ = lean_unbox(v_kind_1121_);
v_res_1128_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1119_, v_k_1120_, v_kind_boxed_1127_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1129_, size_t v_i_1130_, lean_object* v_bs_1131_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_usize_dec_lt(v_i_1130_, v_sz_1129_);
if (v___x_1132_ == 0)
{
return v_bs_1131_;
}
else
{
lean_object* v_v_1133_; lean_object* v_fst_1134_; lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1151_; 
v_v_1133_ = lean_array_uget(v_bs_1131_, v_i_1130_);
v_fst_1134_ = lean_ctor_get(v_v_1133_, 0);
v_snd_1135_ = lean_ctor_get(v_v_1133_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_v_1133_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1137_ = v_v_1133_;
v_isShared_1138_ = v_isSharedCheck_1151_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_inc(v_fst_1134_);
lean_dec(v_v_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1151_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v_bs_x27_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1139_ = lean_unsigned_to_nat(0u);
v_bs_x27_1140_ = lean_array_uset(v_bs_1131_, v_i_1130_, v___x_1139_);
v___x_1141_ = 0;
v___x_1142_ = lean_box(v___x_1141_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1142_);
v___x_1144_ = v___x_1137_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_snd_1135_);
v___x_1144_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_fst_1134_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = ((size_t)1ULL);
v___x_1147_ = lean_usize_add(v_i_1130_, v___x_1146_);
v___x_1148_ = lean_array_uset(v_bs_x27_1140_, v_i_1130_, v___x_1145_);
v_i_1130_ = v___x_1147_;
v_bs_1131_ = v___x_1148_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_bs_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1158_, lean_object* v_k_1159_, uint8_t v_kind_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
size_t v_sz_1166_; size_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_sz_1166_ = lean_array_size(v_declInfos_1158_);
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1166_, v___x_1167_, v_declInfos_1158_);
v___x_1169_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1168_, v_k_1159_, v_kind_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1170_, lean_object* v_k_1171_, lean_object* v_kind_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_kind_boxed_1178_; lean_object* v_res_1179_; 
v_kind_boxed_1178_ = lean_unbox(v_kind_1172_);
v_res_1179_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1170_, v_k_1171_, v_kind_boxed_1178_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1180_, lean_object* v_k_1181_, uint8_t v_kind_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
size_t v_sz_1188_; size_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_sz_1188_ = lean_array_size(v_declInfos_1180_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1188_, v___x_1189_, v_declInfos_1180_);
v___x_1191_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1190_, v_k_1181_, v_kind_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1192_, lean_object* v_k_1193_, lean_object* v_kind_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_kind_boxed_1200_; lean_object* v_res_1201_; 
v_kind_boxed_1200_ = lean_unbox(v_kind_1194_);
v_res_1201_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1192_, v_k_1193_, v_kind_boxed_1200_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1203_, lean_object* v_dummy_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v_motive_1208_, lean_object* v_zs1_1209_, uint8_t v_isZero_1210_, uint8_t v___x_1211_, uint8_t v___x_1212_, lean_object* v___x_1213_, lean_object* v_j_1214_, lean_object* v_zs2_1215_, lean_object* v_ctorRet2_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v___x_1222_ = lean_whnf(v_ctorRet2_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; lean_object* v_nargs_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = l_Lean_mkAppN(v___x_1203_, v_zs2_1215_);
v_nargs_1225_ = l_Lean_Expr_getAppNumArgs(v_a_1223_);
lean_inc(v_nargs_1225_);
v___x_1226_ = lean_mk_array(v_nargs_1225_, v_dummy_1204_);
v___x_1227_ = lean_nat_sub(v_nargs_1225_, v___x_1205_);
lean_dec(v_nargs_1225_);
v___x_1228_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1223_, v___x_1226_, v___x_1227_);
v___x_1229_ = lean_array_get_size(v___x_1228_);
v___x_1230_ = l_Array_toSubarray___redArg(v___x_1228_, v___x_1206_, v___x_1229_);
v___x_1231_ = l_Subarray_copy___redArg(v___x_1230_);
v___x_1232_ = lean_array_push(v___x_1231_, v___x_1224_);
v___x_1233_ = l_Array_append___redArg(v___x_1207_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_mkAppN(v_motive_1208_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = l_Array_append___redArg(v_zs1_1209_, v_zs2_1215_);
v___x_1236_ = l_Lean_Meta_mkForallFVars(v___x_1235_, v___x_1234_, v_isZero_1210_, v___x_1211_, v___x_1211_, v___x_1212_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec_ref(v___x_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1256_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1256_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1256_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___y_1242_; 
if (lean_obj_tag(v___x_1213_) == 1)
{
lean_object* v_str_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_str_1247_ = lean_ctor_get(v___x_1213_, 1);
lean_inc_ref(v_str_1247_);
lean_dec_ref(v___x_1213_);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_Name_str___override(v___x_1248_, v_str_1247_);
v___y_1242_ = v___x_1249_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v___x_1213_);
v___x_1250_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1251_ = lean_nat_add(v_j_1214_, v___x_1205_);
v___x_1252_ = l_Nat_reprFast(v___x_1251_);
v___x_1253_ = lean_string_append(v___x_1250_, v___x_1252_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Lean_Name_str___override(v___x_1254_, v___x_1253_);
v___y_1242_ = v___x_1255_;
goto v___jp_1241_;
}
v___jp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___y_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1243_);
v___x_1245_ = v___x_1239_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v___x_1213_);
v_a_1257_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1236_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1236_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v___x_1213_);
lean_dec_ref(v_zs1_1209_);
lean_dec_ref(v_motive_1208_);
lean_dec_ref(v___x_1207_);
lean_dec(v___x_1206_);
lean_dec_ref(v_dummy_1204_);
lean_dec_ref(v___x_1203_);
v_a_1265_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1222_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1222_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1273_ = _args[0];
lean_object* v_dummy_1274_ = _args[1];
lean_object* v___x_1275_ = _args[2];
lean_object* v___x_1276_ = _args[3];
lean_object* v___x_1277_ = _args[4];
lean_object* v_motive_1278_ = _args[5];
lean_object* v_zs1_1279_ = _args[6];
lean_object* v_isZero_1280_ = _args[7];
lean_object* v___x_1281_ = _args[8];
lean_object* v___x_1282_ = _args[9];
lean_object* v___x_1283_ = _args[10];
lean_object* v_j_1284_ = _args[11];
lean_object* v_zs2_1285_ = _args[12];
lean_object* v_ctorRet2_1286_ = _args[13];
lean_object* v___y_1287_ = _args[14];
lean_object* v___y_1288_ = _args[15];
lean_object* v___y_1289_ = _args[16];
lean_object* v___y_1290_ = _args[17];
lean_object* v___y_1291_ = _args[18];
_start:
{
uint8_t v_isZero_boxed_1292_; uint8_t v___x_21842__boxed_1293_; uint8_t v___x_21843__boxed_1294_; lean_object* v_res_1295_; 
v_isZero_boxed_1292_ = lean_unbox(v_isZero_1280_);
v___x_21842__boxed_1293_ = lean_unbox(v___x_1281_);
v___x_21843__boxed_1294_ = lean_unbox(v___x_1282_);
v_res_1295_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1273_, v_dummy_1274_, v___x_1275_, v___x_1276_, v___x_1277_, v_motive_1278_, v_zs1_1279_, v_isZero_boxed_1292_, v___x_21842__boxed_1293_, v___x_21843__boxed_1294_, v___x_1283_, v_j_1284_, v_zs2_1285_, v_ctorRet2_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_zs2_1285_);
lean_dec(v_j_1284_);
lean_dec(v___x_1275_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v_motive_1299_, uint8_t v_isZero_1300_, uint8_t v___x_1301_, uint8_t v___x_1302_, lean_object* v___x_1303_, lean_object* v_j_1304_, lean_object* v_a_1305_, lean_object* v_zs1_1306_, lean_object* v_ctorRet1_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
lean_inc(v___y_1311_);
lean_inc_ref(v___y_1310_);
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
v___x_1313_ = lean_whnf(v_ctorRet1_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v_dummy_1316_; lean_object* v_nargs_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
lean_inc_ref(v___x_1296_);
v___x_1315_ = l_Lean_mkAppN(v___x_1296_, v_zs1_1306_);
v_dummy_1316_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1317_ = l_Lean_Expr_getAppNumArgs(v_a_1314_);
lean_inc(v_nargs_1317_);
v___x_1318_ = lean_mk_array(v_nargs_1317_, v_dummy_1316_);
v___x_1319_ = lean_nat_sub(v_nargs_1317_, v___x_1297_);
lean_dec(v_nargs_1317_);
v___x_1320_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1314_, v___x_1318_, v___x_1319_);
v___x_1321_ = lean_array_get_size(v___x_1320_);
lean_inc(v___x_1298_);
v___x_1322_ = l_Array_toSubarray___redArg(v___x_1320_, v___x_1298_, v___x_1321_);
v___x_1323_ = l_Subarray_copy___redArg(v___x_1322_);
v___x_1324_ = lean_array_push(v___x_1323_, v___x_1315_);
v___x_1325_ = lean_box(v_isZero_1300_);
v___x_1326_ = lean_box(v___x_1301_);
v___x_1327_ = lean_box(v___x_1302_);
v___f_1328_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1328_, 0, v___x_1296_);
lean_closure_set(v___f_1328_, 1, v_dummy_1316_);
lean_closure_set(v___f_1328_, 2, v___x_1297_);
lean_closure_set(v___f_1328_, 3, v___x_1298_);
lean_closure_set(v___f_1328_, 4, v___x_1324_);
lean_closure_set(v___f_1328_, 5, v_motive_1299_);
lean_closure_set(v___f_1328_, 6, v_zs1_1306_);
lean_closure_set(v___f_1328_, 7, v___x_1325_);
lean_closure_set(v___f_1328_, 8, v___x_1326_);
lean_closure_set(v___f_1328_, 9, v___x_1327_);
lean_closure_set(v___f_1328_, 10, v___x_1303_);
lean_closure_set(v___f_1328_, 11, v_j_1304_);
v___x_1329_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1305_, v___f_1328_, v_isZero_1300_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1329_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_zs1_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_j_1304_);
lean_dec(v___x_1303_);
lean_dec_ref(v_motive_1299_);
lean_dec(v___x_1298_);
lean_dec(v___x_1297_);
lean_dec_ref(v___x_1296_);
v_a_1330_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1313_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1313_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1338_ = _args[0];
lean_object* v___x_1339_ = _args[1];
lean_object* v___x_1340_ = _args[2];
lean_object* v_motive_1341_ = _args[3];
lean_object* v_isZero_1342_ = _args[4];
lean_object* v___x_1343_ = _args[5];
lean_object* v___x_1344_ = _args[6];
lean_object* v___x_1345_ = _args[7];
lean_object* v_j_1346_ = _args[8];
lean_object* v_a_1347_ = _args[9];
lean_object* v_zs1_1348_ = _args[10];
lean_object* v_ctorRet1_1349_ = _args[11];
lean_object* v___y_1350_ = _args[12];
lean_object* v___y_1351_ = _args[13];
lean_object* v___y_1352_ = _args[14];
lean_object* v___y_1353_ = _args[15];
lean_object* v___y_1354_ = _args[16];
_start:
{
uint8_t v_isZero_boxed_1355_; uint8_t v___x_21980__boxed_1356_; uint8_t v___x_21981__boxed_1357_; lean_object* v_res_1358_; 
v_isZero_boxed_1355_ = lean_unbox(v_isZero_1342_);
v___x_21980__boxed_1356_ = lean_unbox(v___x_1343_);
v___x_21981__boxed_1357_ = lean_unbox(v___x_1344_);
v_res_1358_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1338_, v___x_1339_, v___x_1340_, v_motive_1341_, v_isZero_boxed_1355_, v___x_21980__boxed_1356_, v___x_21981__boxed_1357_, v___x_1345_, v_j_1346_, v_a_1347_, v_zs1_1348_, v_ctorRet1_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1359_, lean_object* v_params_1360_, lean_object* v___x_1361_, lean_object* v_motive_1362_, lean_object* v_as_1363_, lean_object* v_i_1364_, lean_object* v_j_1365_, lean_object* v_bs_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_zero_1372_; uint8_t v_isZero_1373_; 
v_zero_1372_ = lean_unsigned_to_nat(0u);
v_isZero_1373_ = lean_nat_dec_eq(v_i_1364_, v_zero_1372_);
if (v_isZero_1373_ == 1)
{
lean_object* v___x_1374_; 
lean_dec(v_j_1365_);
lean_dec(v_i_1364_);
lean_dec_ref(v_motive_1362_);
lean_dec(v___x_1361_);
lean_dec(v_tail_1359_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_bs_1366_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = lean_array_fget_borrowed(v_as_1363_, v_j_1365_);
lean_inc(v_tail_1359_);
lean_inc(v___x_1375_);
v___x_1376_ = l_Lean_mkConst(v___x_1375_, v_tail_1359_);
v___x_1377_ = l_Lean_mkAppN(v___x_1376_, v_params_1360_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc_ref(v___x_1377_);
v___x_1378_ = lean_infer_type(v___x_1377_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_n(v_a_1379_, 2);
lean_dec_ref(v___x_1378_);
v___x_1380_ = 1;
v___x_1381_ = 1;
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_box(v_isZero_1373_);
v___x_1384_ = lean_box(v___x_1380_);
v___x_1385_ = lean_box(v___x_1381_);
lean_inc(v_j_1365_);
lean_inc(v___x_1375_);
lean_inc_ref(v_motive_1362_);
lean_inc(v___x_1361_);
v___f_1386_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1386_, 0, v___x_1377_);
lean_closure_set(v___f_1386_, 1, v___x_1382_);
lean_closure_set(v___f_1386_, 2, v___x_1361_);
lean_closure_set(v___f_1386_, 3, v_motive_1362_);
lean_closure_set(v___f_1386_, 4, v___x_1383_);
lean_closure_set(v___f_1386_, 5, v___x_1384_);
lean_closure_set(v___f_1386_, 6, v___x_1385_);
lean_closure_set(v___f_1386_, 7, v___x_1375_);
lean_closure_set(v___f_1386_, 8, v_j_1365_);
lean_closure_set(v___f_1386_, 9, v_a_1379_);
v___x_1387_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1379_, v___f_1386_, v_isZero_1373_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v_n_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
v_n_1389_ = lean_nat_sub(v_i_1364_, v___x_1382_);
lean_dec(v_i_1364_);
v___x_1390_ = lean_nat_add(v_j_1365_, v___x_1382_);
lean_dec(v_j_1365_);
v___x_1391_ = lean_array_push(v_bs_1366_, v_a_1388_);
v_i_1364_ = v_n_1389_;
v_j_1365_ = v___x_1390_;
v_bs_1366_ = v___x_1391_;
goto _start;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_bs_1366_);
lean_dec(v_j_1365_);
lean_dec(v_i_1364_);
lean_dec_ref(v_motive_1362_);
lean_dec(v___x_1361_);
lean_dec(v_tail_1359_);
v_a_1393_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1387_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1387_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___x_1377_);
lean_dec_ref(v_bs_1366_);
lean_dec(v_j_1365_);
lean_dec(v_i_1364_);
lean_dec_ref(v_motive_1362_);
lean_dec(v___x_1361_);
lean_dec(v_tail_1359_);
v_a_1401_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1378_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1378_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1409_, lean_object* v_params_1410_, lean_object* v___x_1411_, lean_object* v_motive_1412_, lean_object* v_as_1413_, lean_object* v_i_1414_, lean_object* v_j_1415_, lean_object* v_bs_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1409_, v_params_1410_, v___x_1411_, v_motive_1412_, v_as_1413_, v_i_1414_, v_j_1415_, v_bs_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v_as_1413_);
lean_dec_ref(v_params_1410_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1423_, lean_object* v_tail_1424_, lean_object* v_params_1425_, lean_object* v_numParams_1426_, lean_object* v_indName_1427_, lean_object* v_ism1_1428_, lean_object* v_ism2_1429_, lean_object* v___x_1430_, uint8_t v___x_1431_, uint8_t v___x_1432_, uint8_t v___x_1433_, lean_object* v_val_1434_, lean_object* v___x_1435_, lean_object* v___x_1436_, lean_object* v_name_1437_, lean_object* v___x_1438_, lean_object* v_motive_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1445_ = lean_array_mk(v_ctors_1423_);
v___x_1446_ = lean_array_get_size(v___x_1445_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_mk_empty_array_with_capacity(v___x_1446_);
lean_inc_ref(v_motive_1439_);
lean_inc(v_numParams_1426_);
lean_inc(v_tail_1424_);
v___x_1449_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1424_, v_params_1425_, v_numParams_1426_, v_motive_1439_, v___x_1445_, v___x_1446_, v___x_1447_, v___x_1448_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___f_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = lean_box(v___x_1431_);
v___x_1452_ = lean_box(v___x_1432_);
v___x_1453_ = lean_box(v___x_1433_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1454_, 0, v_indName_1427_);
lean_closure_set(v___f_1454_, 1, v_tail_1424_);
lean_closure_set(v___f_1454_, 2, v_params_1425_);
lean_closure_set(v___f_1454_, 3, v_ism1_1428_);
lean_closure_set(v___f_1454_, 4, v_ism2_1429_);
lean_closure_set(v___f_1454_, 5, v_motive_1439_);
lean_closure_set(v___f_1454_, 6, v___x_1430_);
lean_closure_set(v___f_1454_, 7, v___x_1451_);
lean_closure_set(v___f_1454_, 8, v___x_1452_);
lean_closure_set(v___f_1454_, 9, v___x_1453_);
lean_closure_set(v___f_1454_, 10, v___x_1445_);
lean_closure_set(v___f_1454_, 11, v_numParams_1426_);
lean_closure_set(v___f_1454_, 12, v_val_1434_);
lean_closure_set(v___f_1454_, 13, v___x_1435_);
lean_closure_set(v___f_1454_, 14, v___x_1436_);
lean_closure_set(v___f_1454_, 15, v_name_1437_);
lean_closure_set(v___f_1454_, 16, v___x_1438_);
v___x_1455_ = 0;
v___x_1456_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1450_, v___f_1454_, v___x_1455_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1456_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v___x_1445_);
lean_dec_ref(v_motive_1439_);
lean_dec(v___x_1438_);
lean_dec(v_name_1437_);
lean_dec(v___x_1436_);
lean_dec(v___x_1435_);
lean_dec_ref(v_val_1434_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_ism2_1429_);
lean_dec_ref(v_ism1_1428_);
lean_dec(v_indName_1427_);
lean_dec(v_numParams_1426_);
lean_dec_ref(v_params_1425_);
lean_dec(v_tail_1424_);
v_a_1457_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1449_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1449_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1465_ = _args[0];
lean_object* v_tail_1466_ = _args[1];
lean_object* v_params_1467_ = _args[2];
lean_object* v_numParams_1468_ = _args[3];
lean_object* v_indName_1469_ = _args[4];
lean_object* v_ism1_1470_ = _args[5];
lean_object* v_ism2_1471_ = _args[6];
lean_object* v___x_1472_ = _args[7];
lean_object* v___x_1473_ = _args[8];
lean_object* v___x_1474_ = _args[9];
lean_object* v___x_1475_ = _args[10];
lean_object* v_val_1476_ = _args[11];
lean_object* v___x_1477_ = _args[12];
lean_object* v___x_1478_ = _args[13];
lean_object* v_name_1479_ = _args[14];
lean_object* v___x_1480_ = _args[15];
lean_object* v_motive_1481_ = _args[16];
lean_object* v___y_1482_ = _args[17];
lean_object* v___y_1483_ = _args[18];
lean_object* v___y_1484_ = _args[19];
lean_object* v___y_1485_ = _args[20];
lean_object* v___y_1486_ = _args[21];
_start:
{
uint8_t v___x_22153__boxed_1487_; uint8_t v___x_22154__boxed_1488_; uint8_t v___x_22155__boxed_1489_; lean_object* v_res_1490_; 
v___x_22153__boxed_1487_ = lean_unbox(v___x_1473_);
v___x_22154__boxed_1488_ = lean_unbox(v___x_1474_);
v___x_22155__boxed_1489_ = lean_unbox(v___x_1475_);
v_res_1490_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1465_, v_tail_1466_, v_params_1467_, v_numParams_1468_, v_indName_1469_, v_ism1_1470_, v_ism2_1471_, v___x_1472_, v___x_22153__boxed_1487_, v___x_22154__boxed_1488_, v___x_22155__boxed_1489_, v_val_1476_, v___x_1477_, v___x_1478_, v_name_1479_, v___x_1480_, v_motive_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1494_, lean_object* v_head_1495_, lean_object* v_ctors_1496_, lean_object* v_tail_1497_, lean_object* v_params_1498_, lean_object* v_numParams_1499_, lean_object* v_indName_1500_, lean_object* v_val_1501_, lean_object* v___x_1502_, lean_object* v___x_1503_, lean_object* v_name_1504_, lean_object* v___x_1505_, lean_object* v_ism2_1506_, lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
lean_inc_ref(v_ism1_1494_);
v___x_1513_ = l_Array_append___redArg(v_ism1_1494_, v_ism2_1506_);
v___x_1514_ = l_Lean_mkSort(v_head_1495_);
v___x_1515_ = 0;
v___x_1516_ = 1;
v___x_1517_ = 1;
v___x_1518_ = l_Lean_Meta_mkForallFVars(v___x_1513_, v___x_1514_, v___x_1515_, v___x_1516_, v___x_1516_, v___x_1517_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = lean_box(v___x_1515_);
v___x_1521_ = lean_box(v___x_1516_);
v___x_1522_ = lean_box(v___x_1517_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1523_, 0, v_ctors_1496_);
lean_closure_set(v___f_1523_, 1, v_tail_1497_);
lean_closure_set(v___f_1523_, 2, v_params_1498_);
lean_closure_set(v___f_1523_, 3, v_numParams_1499_);
lean_closure_set(v___f_1523_, 4, v_indName_1500_);
lean_closure_set(v___f_1523_, 5, v_ism1_1494_);
lean_closure_set(v___f_1523_, 6, v_ism2_1506_);
lean_closure_set(v___f_1523_, 7, v___x_1513_);
lean_closure_set(v___f_1523_, 8, v___x_1520_);
lean_closure_set(v___f_1523_, 9, v___x_1521_);
lean_closure_set(v___f_1523_, 10, v___x_1522_);
lean_closure_set(v___f_1523_, 11, v_val_1501_);
lean_closure_set(v___f_1523_, 12, v___x_1502_);
lean_closure_set(v___f_1523_, 13, v___x_1503_);
lean_closure_set(v___f_1523_, 14, v_name_1504_);
lean_closure_set(v___f_1523_, 15, v___x_1505_);
v___x_1524_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1525_ = 0;
v___x_1526_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1524_, v___x_1517_, v_a_1519_, v___f_1523_, v___x_1525_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1526_;
}
else
{
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_ism2_1506_);
lean_dec(v___x_1505_);
lean_dec(v_name_1504_);
lean_dec(v___x_1503_);
lean_dec(v___x_1502_);
lean_dec_ref(v_val_1501_);
lean_dec(v_indName_1500_);
lean_dec(v_numParams_1499_);
lean_dec_ref(v_params_1498_);
lean_dec(v_tail_1497_);
lean_dec(v_ctors_1496_);
lean_dec_ref(v_ism1_1494_);
return v___x_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1527_ = _args[0];
lean_object* v_head_1528_ = _args[1];
lean_object* v_ctors_1529_ = _args[2];
lean_object* v_tail_1530_ = _args[3];
lean_object* v_params_1531_ = _args[4];
lean_object* v_numParams_1532_ = _args[5];
lean_object* v_indName_1533_ = _args[6];
lean_object* v_val_1534_ = _args[7];
lean_object* v___x_1535_ = _args[8];
lean_object* v___x_1536_ = _args[9];
lean_object* v_name_1537_ = _args[10];
lean_object* v___x_1538_ = _args[11];
lean_object* v_ism2_1539_ = _args[12];
lean_object* v_x_1540_ = _args[13];
lean_object* v___y_1541_ = _args[14];
lean_object* v___y_1542_ = _args[15];
lean_object* v___y_1543_ = _args[16];
lean_object* v___y_1544_ = _args[17];
lean_object* v___y_1545_ = _args[18];
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1527_, v_head_1528_, v_ctors_1529_, v_tail_1530_, v_params_1531_, v_numParams_1532_, v_indName_1533_, v_val_1534_, v___x_1535_, v___x_1536_, v_name_1537_, v___x_1538_, v_ism2_1539_, v_x_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec_ref(v_x_1540_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1547_, lean_object* v_ctors_1548_, lean_object* v_tail_1549_, lean_object* v_params_1550_, lean_object* v_numParams_1551_, lean_object* v_indName_1552_, lean_object* v_val_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v_name_1556_, lean_object* v___x_1557_, lean_object* v_t_1558_, lean_object* v___x_1559_, lean_object* v_ism1_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___f_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1567_, 0, v_ism1_1560_);
lean_closure_set(v___f_1567_, 1, v_head_1547_);
lean_closure_set(v___f_1567_, 2, v_ctors_1548_);
lean_closure_set(v___f_1567_, 3, v_tail_1549_);
lean_closure_set(v___f_1567_, 4, v_params_1550_);
lean_closure_set(v___f_1567_, 5, v_numParams_1551_);
lean_closure_set(v___f_1567_, 6, v_indName_1552_);
lean_closure_set(v___f_1567_, 7, v_val_1553_);
lean_closure_set(v___f_1567_, 8, v___x_1554_);
lean_closure_set(v___f_1567_, 9, v___x_1555_);
lean_closure_set(v___f_1567_, 10, v_name_1556_);
lean_closure_set(v___f_1567_, 11, v___x_1557_);
v___x_1568_ = 0;
v___x_1569_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1558_, v___x_1559_, v___f_1567_, v___x_1568_, v___x_1568_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1570_ = _args[0];
lean_object* v_ctors_1571_ = _args[1];
lean_object* v_tail_1572_ = _args[2];
lean_object* v_params_1573_ = _args[3];
lean_object* v_numParams_1574_ = _args[4];
lean_object* v_indName_1575_ = _args[5];
lean_object* v_val_1576_ = _args[6];
lean_object* v___x_1577_ = _args[7];
lean_object* v___x_1578_ = _args[8];
lean_object* v_name_1579_ = _args[9];
lean_object* v___x_1580_ = _args[10];
lean_object* v_t_1581_ = _args[11];
lean_object* v___x_1582_ = _args[12];
lean_object* v_ism1_1583_ = _args[13];
lean_object* v_x_1584_ = _args[14];
lean_object* v___y_1585_ = _args[15];
lean_object* v___y_1586_ = _args[16];
lean_object* v___y_1587_ = _args[17];
lean_object* v___y_1588_ = _args[18];
lean_object* v___y_1589_ = _args[19];
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1570_, v_ctors_1571_, v_tail_1572_, v_params_1573_, v_numParams_1574_, v_indName_1575_, v_val_1576_, v___x_1577_, v___x_1578_, v_name_1579_, v___x_1580_, v_t_1581_, v___x_1582_, v_ism1_1583_, v_x_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_x_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1591_, lean_object* v___x_1592_, lean_object* v_head_1593_, lean_object* v_ctors_1594_, lean_object* v_tail_1595_, lean_object* v_params_1596_, lean_object* v_numParams_1597_, lean_object* v_indName_1598_, lean_object* v_val_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_name_1602_, lean_object* v_x_1603_, lean_object* v_t_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1610_ = lean_nat_add(v_numIndices_1591_, v___x_1592_);
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_inc_ref(v___x_1611_);
lean_inc_ref(v_t_1604_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1612_, 0, v_head_1593_);
lean_closure_set(v___f_1612_, 1, v_ctors_1594_);
lean_closure_set(v___f_1612_, 2, v_tail_1595_);
lean_closure_set(v___f_1612_, 3, v_params_1596_);
lean_closure_set(v___f_1612_, 4, v_numParams_1597_);
lean_closure_set(v___f_1612_, 5, v_indName_1598_);
lean_closure_set(v___f_1612_, 6, v_val_1599_);
lean_closure_set(v___f_1612_, 7, v___x_1600_);
lean_closure_set(v___f_1612_, 8, v___x_1601_);
lean_closure_set(v___f_1612_, 9, v_name_1602_);
lean_closure_set(v___f_1612_, 10, v___x_1592_);
lean_closure_set(v___f_1612_, 11, v_t_1604_);
lean_closure_set(v___f_1612_, 12, v___x_1611_);
v___x_1613_ = 0;
v___x_1614_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1604_, v___x_1611_, v___f_1612_, v___x_1613_, v___x_1613_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1615_ = _args[0];
lean_object* v___x_1616_ = _args[1];
lean_object* v_head_1617_ = _args[2];
lean_object* v_ctors_1618_ = _args[3];
lean_object* v_tail_1619_ = _args[4];
lean_object* v_params_1620_ = _args[5];
lean_object* v_numParams_1621_ = _args[6];
lean_object* v_indName_1622_ = _args[7];
lean_object* v_val_1623_ = _args[8];
lean_object* v___x_1624_ = _args[9];
lean_object* v___x_1625_ = _args[10];
lean_object* v_name_1626_ = _args[11];
lean_object* v_x_1627_ = _args[12];
lean_object* v_t_1628_ = _args[13];
lean_object* v___y_1629_ = _args[14];
lean_object* v___y_1630_ = _args[15];
lean_object* v___y_1631_ = _args[16];
lean_object* v___y_1632_ = _args[17];
lean_object* v___y_1633_ = _args[18];
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1615_, v___x_1616_, v_head_1617_, v_ctors_1618_, v_tail_1619_, v_params_1620_, v_numParams_1621_, v_indName_1622_, v_val_1623_, v___x_1624_, v___x_1625_, v_name_1626_, v_x_1627_, v_t_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_x_1627_);
lean_dec(v_numIndices_1615_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1637_, lean_object* v_head_1638_, lean_object* v_ctors_1639_, lean_object* v_tail_1640_, lean_object* v_numParams_1641_, lean_object* v_indName_1642_, lean_object* v_val_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v_name_1646_, lean_object* v_params_1647_, lean_object* v_t_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1655_, 0, v_numIndices_1637_);
lean_closure_set(v___f_1655_, 1, v___x_1654_);
lean_closure_set(v___f_1655_, 2, v_head_1638_);
lean_closure_set(v___f_1655_, 3, v_ctors_1639_);
lean_closure_set(v___f_1655_, 4, v_tail_1640_);
lean_closure_set(v___f_1655_, 5, v_params_1647_);
lean_closure_set(v___f_1655_, 6, v_numParams_1641_);
lean_closure_set(v___f_1655_, 7, v_indName_1642_);
lean_closure_set(v___f_1655_, 8, v_val_1643_);
lean_closure_set(v___f_1655_, 9, v___x_1644_);
lean_closure_set(v___f_1655_, 10, v___x_1645_);
lean_closure_set(v___f_1655_, 11, v_name_1646_);
v___x_1656_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1657_ = 0;
v___x_1658_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1648_, v___x_1656_, v___f_1655_, v___x_1657_, v___x_1657_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1659_ = _args[0];
lean_object* v_head_1660_ = _args[1];
lean_object* v_ctors_1661_ = _args[2];
lean_object* v_tail_1662_ = _args[3];
lean_object* v_numParams_1663_ = _args[4];
lean_object* v_indName_1664_ = _args[5];
lean_object* v_val_1665_ = _args[6];
lean_object* v___x_1666_ = _args[7];
lean_object* v___x_1667_ = _args[8];
lean_object* v_name_1668_ = _args[9];
lean_object* v_params_1669_ = _args[10];
lean_object* v_t_1670_ = _args[11];
lean_object* v___y_1671_ = _args[12];
lean_object* v___y_1672_ = _args[13];
lean_object* v___y_1673_ = _args[14];
lean_object* v___y_1674_ = _args[15];
lean_object* v___y_1675_ = _args[16];
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1659_, v_head_1660_, v_ctors_1661_, v_tail_1662_, v_numParams_1663_, v_indName_1664_, v_val_1665_, v___x_1666_, v___x_1667_, v_name_1668_, v_params_1669_, v_t_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1677_, lean_object* v_declName_1678_, lean_object* v_levelParams_1679_, uint8_t v___x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc_ref(v_a_1677_);
v___x_1686_ = lean_infer_type(v_a_1677_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_box(1);
v___x_1689_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1678_, v_levelParams_1679_, v_a_1687_, v_a_1677_, v___x_1688_, v___y_1684_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_addDecl(v___x_1695_, v___x_1680_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_levelParams_1679_);
lean_dec(v_declName_1678_);
lean_dec_ref(v_a_1677_);
v_a_1699_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1686_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1686_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1707_, lean_object* v_declName_1708_, lean_object* v_levelParams_1709_, lean_object* v___x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_22445__boxed_1716_; lean_object* v_res_1717_; 
v___x_22445__boxed_1716_ = lean_unbox(v___x_1710_);
v_res_1717_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1707_, v_declName_1708_, v_levelParams_1709_, v___x_22445__boxed_1716_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
if (lean_obj_tag(v_a_1718_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = l_List_reverse___redArg(v_a_1719_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_head_1721_ = lean_ctor_get(v_a_1718_, 0);
v_tail_1722_ = lean_ctor_get(v_a_1718_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_a_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v_a_1718_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_tail_1722_);
lean_inc(v_head_1721_);
lean_dec(v_a_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_mkLevelParam(v_head_1721_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v_a_1719_);
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1719_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v_a_1718_ = v_tail_1722_;
v_a_1719_ = v___x_1728_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v___x_1740_; lean_object* v_mctx_1741_; lean_object* v_lctx_1742_; lean_object* v_options_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1738_ = lean_st_ref_get(v___y_1736_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = lean_st_ref_get(v___y_1734_);
v_mctx_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc_ref(v_mctx_1741_);
lean_dec(v___x_1740_);
v_lctx_1742_ = lean_ctor_get(v___y_1733_, 2);
v_options_1743_ = lean_ctor_get(v___y_1735_, 2);
lean_inc_ref(v_options_1743_);
lean_inc_ref(v_lctx_1742_);
v___x_1744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1744_, 0, v_env_1739_);
lean_ctor_set(v___x_1744_, 1, v_mctx_1741_);
lean_ctor_set(v___x_1744_, 2, v_lctx_1742_);
lean_ctor_set(v___x_1744_, 3, v_options_1743_);
v___x_1745_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_msgData_1732_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_ref_1760_; lean_object* v___x_1761_; lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
v_ref_1760_ = lean_ctor_get(v___y_1757_, 5);
v___x_1761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_inc(v_ref_1760_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_ref_1760_);
lean_ctor_set(v___x_1766_, 1, v_a_1762_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1778_, lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_fileName_1785_; lean_object* v_fileMap_1786_; lean_object* v_options_1787_; lean_object* v_currRecDepth_1788_; lean_object* v_maxRecDepth_1789_; lean_object* v_ref_1790_; lean_object* v_currNamespace_1791_; lean_object* v_openDecls_1792_; lean_object* v_initHeartbeats_1793_; lean_object* v_maxHeartbeats_1794_; lean_object* v_quotContext_1795_; lean_object* v_currMacroScope_1796_; uint8_t v_diag_1797_; lean_object* v_cancelTk_x3f_1798_; uint8_t v_suppressElabErrors_1799_; lean_object* v_inheritedTraceOptions_1800_; lean_object* v_ref_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_fileName_1785_ = lean_ctor_get(v___y_1782_, 0);
v_fileMap_1786_ = lean_ctor_get(v___y_1782_, 1);
v_options_1787_ = lean_ctor_get(v___y_1782_, 2);
v_currRecDepth_1788_ = lean_ctor_get(v___y_1782_, 3);
v_maxRecDepth_1789_ = lean_ctor_get(v___y_1782_, 4);
v_ref_1790_ = lean_ctor_get(v___y_1782_, 5);
v_currNamespace_1791_ = lean_ctor_get(v___y_1782_, 6);
v_openDecls_1792_ = lean_ctor_get(v___y_1782_, 7);
v_initHeartbeats_1793_ = lean_ctor_get(v___y_1782_, 8);
v_maxHeartbeats_1794_ = lean_ctor_get(v___y_1782_, 9);
v_quotContext_1795_ = lean_ctor_get(v___y_1782_, 10);
v_currMacroScope_1796_ = lean_ctor_get(v___y_1782_, 11);
v_diag_1797_ = lean_ctor_get_uint8(v___y_1782_, sizeof(void*)*14);
v_cancelTk_x3f_1798_ = lean_ctor_get(v___y_1782_, 12);
v_suppressElabErrors_1799_ = lean_ctor_get_uint8(v___y_1782_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1800_ = lean_ctor_get(v___y_1782_, 13);
v_ref_1801_ = l_Lean_replaceRef(v_ref_1778_, v_ref_1790_);
lean_inc_ref(v_inheritedTraceOptions_1800_);
lean_inc(v_cancelTk_x3f_1798_);
lean_inc(v_currMacroScope_1796_);
lean_inc(v_quotContext_1795_);
lean_inc(v_maxHeartbeats_1794_);
lean_inc(v_initHeartbeats_1793_);
lean_inc(v_openDecls_1792_);
lean_inc(v_currNamespace_1791_);
lean_inc(v_maxRecDepth_1789_);
lean_inc(v_currRecDepth_1788_);
lean_inc_ref(v_options_1787_);
lean_inc_ref(v_fileMap_1786_);
lean_inc_ref(v_fileName_1785_);
v___x_1802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1802_, 0, v_fileName_1785_);
lean_ctor_set(v___x_1802_, 1, v_fileMap_1786_);
lean_ctor_set(v___x_1802_, 2, v_options_1787_);
lean_ctor_set(v___x_1802_, 3, v_currRecDepth_1788_);
lean_ctor_set(v___x_1802_, 4, v_maxRecDepth_1789_);
lean_ctor_set(v___x_1802_, 5, v_ref_1801_);
lean_ctor_set(v___x_1802_, 6, v_currNamespace_1791_);
lean_ctor_set(v___x_1802_, 7, v_openDecls_1792_);
lean_ctor_set(v___x_1802_, 8, v_initHeartbeats_1793_);
lean_ctor_set(v___x_1802_, 9, v_maxHeartbeats_1794_);
lean_ctor_set(v___x_1802_, 10, v_quotContext_1795_);
lean_ctor_set(v___x_1802_, 11, v_currMacroScope_1796_);
lean_ctor_set(v___x_1802_, 12, v_cancelTk_x3f_1798_);
lean_ctor_set(v___x_1802_, 13, v_inheritedTraceOptions_1800_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*14, v_diag_1797_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*14 + 1, v_suppressElabErrors_1799_);
v___x_1803_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1779_, v___y_1780_, v___y_1781_, v___x_1802_, v___y_1783_);
lean_dec_ref(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1804_, lean_object* v_msg_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1804_, v_msg_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v_ref_1804_);
return v_res_1811_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
lean_ctor_set(v___x_1817_, 2, v___x_1816_);
lean_ctor_set(v___x_1817_, 3, v___x_1816_);
lean_ctor_set(v___x_1817_, 4, v___x_1815_);
lean_ctor_set(v___x_1817_, 5, v___x_1815_);
lean_ctor_set(v___x_1817_, 6, v___x_1815_);
lean_ctor_set(v___x_1817_, 7, v___x_1815_);
lean_ctor_set(v___x_1817_, 8, v___x_1815_);
lean_ctor_set(v___x_1817_, 9, v___x_1815_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_unsigned_to_nat(32u);
v___x_1819_ = lean_mk_empty_array_with_capacity(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = ((size_t)5ULL);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_unsigned_to_nat(32u);
v___x_1824_ = lean_mk_empty_array_with_capacity(v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1826_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
lean_ctor_set(v___x_1826_, 2, v___x_1822_);
lean_ctor_set(v___x_1826_, 3, v___x_1822_);
lean_ctor_set_usize(v___x_1826_, 4, v___x_1821_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1827_ = lean_box(1);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1828_);
lean_ctor_set(v___x_1830_, 2, v___x_1827_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
return v___x_1833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1852_, lean_object* v_declHint_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v_env_1857_; uint8_t v___x_1858_; 
v___x_1856_ = lean_st_ref_get(v___y_1854_);
v_env_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_ref(v_env_1857_);
lean_dec(v___x_1856_);
v___x_1858_ = l_Lean_Name_isAnonymous(v_declHint_1853_);
if (v___x_1858_ == 0)
{
uint8_t v_isExporting_1859_; 
v_isExporting_1859_ = lean_ctor_get_uint8(v_env_1857_, sizeof(void*)*8);
if (v_isExporting_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_msg_1852_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
lean_inc_ref(v_env_1857_);
v___x_1861_ = l_Lean_Environment_setExporting(v_env_1857_, v___x_1858_);
lean_inc(v_declHint_1853_);
lean_inc_ref(v___x_1861_);
v___x_1862_ = l_Lean_Environment_contains(v___x_1861_, v_declHint_1853_, v_isExporting_1859_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_dec_ref(v___x_1861_);
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_msg_1852_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_c_1869_; lean_object* v___x_1870_; 
v___x_1864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1866_ = l_Lean_Options_empty;
v___x_1867_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1861_);
lean_ctor_set(v___x_1867_, 1, v___x_1864_);
lean_ctor_set(v___x_1867_, 2, v___x_1865_);
lean_ctor_set(v___x_1867_, 3, v___x_1866_);
lean_inc(v_declHint_1853_);
v___x_1868_ = l_Lean_MessageData_ofConstName(v_declHint_1853_, v___x_1858_);
v_c_1869_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1869_, 0, v___x_1867_);
lean_ctor_set(v_c_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1857_, v_declHint_1853_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_c_1869_);
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_MessageData_note(v___x_1874_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_msg_1852_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1913_; 
v_val_1878_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1880_ = v___x_1870_;
v_isShared_1881_ = v_isSharedCheck_1913_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_val_1878_);
lean_dec(v___x_1870_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1913_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_mod_1885_; uint8_t v___x_1886_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = l_Lean_Environment_header(v_env_1857_);
lean_dec_ref(v_env_1857_);
v___x_1884_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1883_);
v_mod_1885_ = lean_array_get(v___x_1882_, v___x_1884_, v_val_1878_);
lean_dec(v_val_1878_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_isPrivateName(v_declHint_1853_);
lean_dec(v_declHint_1853_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_c_1869_);
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_ofName(v_mod_1885_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l_Lean_MessageData_note(v___x_1894_);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_msg_1852_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1896_);
v___x_1898_ = v___x_1880_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_c_1869_);
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_MessageData_ofName(v_mod_1885_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_MessageData_note(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_msg_1852_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1909_);
v___x_1911_ = v___x_1880_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1914_; 
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_msg_1852_);
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1915_, lean_object* v_declHint_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1915_, v_declHint_1916_, v___y_1917_);
lean_dec(v___y_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1920_, lean_object* v_declHint_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1937_; 
v___x_1927_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1920_, v_declHint_1921_, v___y_1925_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1932_ = l_Lean_unknownIdentifierMessageTag;
v___x_1933_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1933_);
v___x_1935_ = v___x_1930_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1938_, lean_object* v_declHint_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1938_, v_declHint_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1946_, lean_object* v_msg_1947_, lean_object* v_declHint_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1956_; 
v___x_1954_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1947_, v_declHint_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1954_);
v___x_1956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1946_, v_a_1955_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1957_, lean_object* v_msg_1958_, lean_object* v_declHint_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1957_, v_msg_1958_, v_declHint_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_ref_1957_);
return v_res_1965_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1971_ = l_Lean_stringToMessageData(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1972_, lean_object* v_constName_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1979_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1980_ = 0;
lean_inc(v_constName_1973_);
v___x_1981_ = l_Lean_MessageData_ofConstName(v_constName_1973_, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1979_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1972_, v___x_1984_, v_constName_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1986_, lean_object* v_constName_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1986_, v_constName_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v_ref_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_ref_2000_; lean_object* v___x_2001_; 
v_ref_2000_ = lean_ctor_get(v___y_1997_, 5);
v___x_2001_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2000_, v_constName_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v_env_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = lean_st_ref_get(v___y_2013_);
v_env_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_env_2016_);
lean_dec(v___x_2015_);
v___x_2017_ = 0;
lean_inc(v_constName_2009_);
v___x_2018_ = l_Lean_Environment_findConstVal_x3f(v_env_2016_, v_constName_2009_, v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2019_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_constName_2009_);
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 0);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_val_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2035_, uint8_t v_s_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v_env_2041_; lean_object* v_nextMacroScope_2042_; lean_object* v_ngen_2043_; lean_object* v_auxDeclNGen_2044_; lean_object* v_traceState_2045_; lean_object* v_messages_2046_; lean_object* v_infoState_2047_; lean_object* v_snapshotTasks_2048_; lean_object* v_newDecls_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2078_; 
v___x_2040_ = lean_st_ref_take(v___y_2038_);
v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
v_nextMacroScope_2042_ = lean_ctor_get(v___x_2040_, 1);
v_ngen_2043_ = lean_ctor_get(v___x_2040_, 2);
v_auxDeclNGen_2044_ = lean_ctor_get(v___x_2040_, 3);
v_traceState_2045_ = lean_ctor_get(v___x_2040_, 4);
v_messages_2046_ = lean_ctor_get(v___x_2040_, 6);
v_infoState_2047_ = lean_ctor_get(v___x_2040_, 7);
v_snapshotTasks_2048_ = lean_ctor_get(v___x_2040_, 8);
v_newDecls_2049_ = lean_ctor_get(v___x_2040_, 9);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2040_, 5);
lean_dec(v_unused_2079_);
v___x_2051_ = v___x_2040_;
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_newDecls_2049_);
lean_inc(v_snapshotTasks_2048_);
lean_inc(v_infoState_2047_);
lean_inc(v_messages_2046_);
lean_inc(v_traceState_2045_);
lean_inc(v_auxDeclNGen_2044_);
lean_inc(v_ngen_2043_);
lean_inc(v_nextMacroScope_2042_);
lean_inc(v_env_2041_);
lean_dec(v___x_2040_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2053_ = 0;
v___x_2054_ = lean_box(0);
v___x_2055_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2041_, v_declName_2035_, v_s_2036_, v___x_2053_, v___x_2054_);
v___x_2056_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 5, v___x_2056_);
lean_ctor_set(v___x_2051_, 0, v___x_2055_);
v___x_2058_ = v___x_2051_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_nextMacroScope_2042_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_ngen_2043_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_auxDeclNGen_2044_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_traceState_2045_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_messages_2046_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_infoState_2047_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_snapshotTasks_2048_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v_newDecls_2049_);
v___x_2058_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_mctx_2061_; lean_object* v_zetaDeltaFVarIds_2062_; lean_object* v_postponed_2063_; lean_object* v_diag_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2075_; 
v___x_2059_ = lean_st_ref_set(v___y_2038_, v___x_2058_);
v___x_2060_ = lean_st_ref_take(v___y_2037_);
v_mctx_2061_ = lean_ctor_get(v___x_2060_, 0);
v_zetaDeltaFVarIds_2062_ = lean_ctor_get(v___x_2060_, 2);
v_postponed_2063_ = lean_ctor_get(v___x_2060_, 3);
v_diag_2064_ = lean_ctor_get(v___x_2060_, 4);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2060_, 1);
lean_dec(v_unused_2076_);
v___x_2066_ = v___x_2060_;
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_diag_2064_);
lean_inc(v_postponed_2063_);
lean_inc(v_zetaDeltaFVarIds_2062_);
lean_inc(v_mctx_2061_);
lean_dec(v___x_2060_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_mctx_2061_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_zetaDeltaFVarIds_2062_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_postponed_2063_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_diag_2064_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_st_ref_set(v___y_2037_, v___x_2070_);
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2080_, lean_object* v_s_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v_s_boxed_2085_; lean_object* v_res_2086_; 
v_s_boxed_2085_ = lean_unbox(v_s_2081_);
v_res_2086_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2080_, v_s_boxed_2085_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec(v___y_2082_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = 0;
v___x_2094_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2087_, v___x_2093_, v___y_2089_, v___y_2091_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2107_ = l_Lean_stringToMessageData(v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2111_, lean_object* v_declName_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2118_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2119_ = l_Lean_MessageData_ofName(v_attrName_2111_);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = 0;
v___x_2124_ = l_Lean_MessageData_ofConstName(v_declName_2112_, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2127_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2129_, lean_object* v_declName_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2129_, v_declName_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2143_, lean_object* v_declName_2144_, lean_object* v_asyncPrefix_x3f_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___y_2152_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2145_) == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_MessageData_nil;
v___y_2152_ = v___x_2165_;
goto v___jp_2151_;
}
else
{
lean_object* v_val_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_val_2166_ = lean_ctor_get(v_asyncPrefix_x3f_2145_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_asyncPrefix_x3f_2145_);
v___x_2167_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2168_ = l_Lean_MessageData_ofName(v_val_2166_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___y_2152_ = v___x_2171_;
goto v___jp_2151_;
}
v___jp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2153_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2154_ = l_Lean_MessageData_ofName(v_attrName_2143_);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = 0;
v___x_2159_ = l_Lean_MessageData_ofConstName(v_declName_2144_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___y_2152_);
v___x_2164_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2163_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2172_, lean_object* v_declName_2173_, lean_object* v_asyncPrefix_x3f_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2172_, v_declName_2173_, v_asyncPrefix_x3f_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2181_, lean_object* v_decl_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___x_2232_; lean_object* v_env_2233_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___x_2248_; 
v___x_2232_ = lean_st_ref_get(v___y_2186_);
v_env_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc_ref(v_env_2233_);
lean_dec(v___x_2232_);
v___x_2248_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2233_, v_decl_2182_);
if (lean_obj_tag(v___x_2248_) == 0)
{
v___y_2235_ = v___y_2183_;
v___y_2236_ = v___y_2184_;
v___y_2237_ = v___y_2185_;
v___y_2238_ = v___y_2186_;
goto v___jp_2234_;
}
else
{
lean_object* v_attr_2249_; lean_object* v_toAttributeImplCore_2250_; lean_object* v_name_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v___x_2248_);
lean_dec_ref(v_env_2233_);
v_attr_2249_ = lean_ctor_get(v_attr_2181_, 0);
lean_inc_ref(v_attr_2249_);
lean_dec_ref(v_attr_2181_);
v_toAttributeImplCore_2250_ = lean_ctor_get(v_attr_2249_, 0);
lean_inc_ref(v_toAttributeImplCore_2250_);
lean_dec_ref(v_attr_2249_);
v_name_2251_ = lean_ctor_get(v_toAttributeImplCore_2250_, 1);
lean_inc(v_name_2251_);
lean_dec_ref(v_toAttributeImplCore_2250_);
v___x_2252_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2251_, v_decl_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
return v___x_2252_;
}
v___jp_2188_:
{
lean_object* v___x_2191_; lean_object* v_ext_2192_; lean_object* v_toEnvExtension_2193_; lean_object* v_env_2194_; lean_object* v_nextMacroScope_2195_; lean_object* v_ngen_2196_; lean_object* v_auxDeclNGen_2197_; lean_object* v_traceState_2198_; lean_object* v_messages_2199_; lean_object* v_infoState_2200_; lean_object* v_snapshotTasks_2201_; lean_object* v_newDecls_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2230_; 
v___x_2191_ = lean_st_ref_take(v___y_2190_);
v_ext_2192_ = lean_ctor_get(v_attr_2181_, 1);
lean_inc_ref(v_ext_2192_);
lean_dec_ref(v_attr_2181_);
v_toEnvExtension_2193_ = lean_ctor_get(v_ext_2192_, 0);
v_env_2194_ = lean_ctor_get(v___x_2191_, 0);
v_nextMacroScope_2195_ = lean_ctor_get(v___x_2191_, 1);
v_ngen_2196_ = lean_ctor_get(v___x_2191_, 2);
v_auxDeclNGen_2197_ = lean_ctor_get(v___x_2191_, 3);
v_traceState_2198_ = lean_ctor_get(v___x_2191_, 4);
v_messages_2199_ = lean_ctor_get(v___x_2191_, 6);
v_infoState_2200_ = lean_ctor_get(v___x_2191_, 7);
v_snapshotTasks_2201_ = lean_ctor_get(v___x_2191_, 8);
v_newDecls_2202_ = lean_ctor_get(v___x_2191_, 9);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2191_, 5);
lean_dec(v_unused_2231_);
v___x_2204_ = v___x_2191_;
v_isShared_2205_ = v_isSharedCheck_2230_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_newDecls_2202_);
lean_inc(v_snapshotTasks_2201_);
lean_inc(v_infoState_2200_);
lean_inc(v_messages_2199_);
lean_inc(v_traceState_2198_);
lean_inc(v_auxDeclNGen_2197_);
lean_inc(v_ngen_2196_);
lean_inc(v_nextMacroScope_2195_);
lean_inc(v_env_2194_);
lean_dec(v___x_2191_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2230_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_asyncMode_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v_asyncMode_2206_ = lean_ctor_get(v_toEnvExtension_2193_, 2);
lean_inc(v_asyncMode_2206_);
lean_inc(v_decl_2182_);
v___x_2207_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2192_, v_env_2194_, v_decl_2182_, v_asyncMode_2206_, v_decl_2182_);
lean_dec(v_asyncMode_2206_);
v___x_2208_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 5, v___x_2208_);
lean_ctor_set(v___x_2204_, 0, v___x_2207_);
v___x_2210_ = v___x_2204_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_nextMacroScope_2195_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_ngen_2196_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_auxDeclNGen_2197_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_traceState_2198_);
lean_ctor_set(v_reuseFailAlloc_2229_, 5, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2229_, 6, v_messages_2199_);
lean_ctor_set(v_reuseFailAlloc_2229_, 7, v_infoState_2200_);
lean_ctor_set(v_reuseFailAlloc_2229_, 8, v_snapshotTasks_2201_);
lean_ctor_set(v_reuseFailAlloc_2229_, 9, v_newDecls_2202_);
v___x_2210_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_mctx_2213_; lean_object* v_zetaDeltaFVarIds_2214_; lean_object* v_postponed_2215_; lean_object* v_diag_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2227_; 
v___x_2211_ = lean_st_ref_set(v___y_2190_, v___x_2210_);
v___x_2212_ = lean_st_ref_take(v___y_2189_);
v_mctx_2213_ = lean_ctor_get(v___x_2212_, 0);
v_zetaDeltaFVarIds_2214_ = lean_ctor_get(v___x_2212_, 2);
v_postponed_2215_ = lean_ctor_get(v___x_2212_, 3);
v_diag_2216_ = lean_ctor_get(v___x_2212_, 4);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2212_, 1);
lean_dec(v_unused_2228_);
v___x_2218_ = v___x_2212_;
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_diag_2216_);
lean_inc(v_postponed_2215_);
lean_inc(v_zetaDeltaFVarIds_2214_);
lean_inc(v_mctx_2213_);
lean_dec(v___x_2212_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_mctx_2213_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_zetaDeltaFVarIds_2214_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_postponed_2215_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_diag_2216_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_st_ref_set(v___y_2189_, v___x_2222_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
}
}
}
v___jp_2234_:
{
lean_object* v_ext_2239_; lean_object* v_toEnvExtension_2240_; lean_object* v_attr_2241_; lean_object* v_asyncMode_2242_; uint8_t v___x_2243_; 
v_ext_2239_ = lean_ctor_get(v_attr_2181_, 1);
v_toEnvExtension_2240_ = lean_ctor_get(v_ext_2239_, 0);
v_attr_2241_ = lean_ctor_get(v_attr_2181_, 0);
v_asyncMode_2242_ = lean_ctor_get(v_toEnvExtension_2240_, 2);
lean_inc(v_decl_2182_);
lean_inc_ref(v_env_2233_);
v___x_2243_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2233_, v_decl_2182_, v_asyncMode_2242_);
if (v___x_2243_ == 0)
{
lean_object* v_toAttributeImplCore_2244_; lean_object* v_name_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_inc_ref(v_attr_2241_);
lean_dec_ref(v_attr_2181_);
v_toAttributeImplCore_2244_ = lean_ctor_get(v_attr_2241_, 0);
lean_inc_ref(v_toAttributeImplCore_2244_);
lean_dec_ref(v_attr_2241_);
v_name_2245_ = lean_ctor_get(v_toAttributeImplCore_2244_, 1);
lean_inc(v_name_2245_);
lean_dec_ref(v_toAttributeImplCore_2244_);
v___x_2246_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2233_);
v___x_2247_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2245_, v_decl_2182_, v___x_2246_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v___x_2247_;
}
else
{
lean_dec_ref(v_env_2233_);
v___y_2189_ = v___y_2236_;
v___y_2190_ = v___y_2238_;
goto v___jp_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2253_, lean_object* v_decl_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2253_, v_decl_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v_env_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = lean_st_ref_get(v___y_2265_);
v_env_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_ref(v_env_2268_);
lean_dec(v___x_2267_);
v___x_2269_ = 0;
lean_inc(v_constName_2261_);
v___x_2270_ = l_Lean_Environment_find_x3f(v_env_2268_, v_constName_2261_, v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2271_;
}
else
{
lean_object* v_val_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_constName_2261_);
v_val_2272_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2270_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_val_2272_);
lean_dec(v___x_2270_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 0);
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_val_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2286_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2290_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2291_ = lean_unsigned_to_nat(58u);
v___x_2292_ = lean_unsigned_to_nat(33u);
v___x_2293_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2294_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2295_ = l_mkPanicMessageWithDecl(v___x_2294_, v___x_2293_, v___x_2292_, v___x_2291_, v___x_2290_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2297_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2298_ = lean_unsigned_to_nat(60u);
v___x_2299_ = lean_unsigned_to_nat(30u);
v___x_2300_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2301_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2302_ = l_mkPanicMessageWithDecl(v___x_2301_, v___x_2300_, v___x_2299_, v___x_2298_, v___x_2297_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2303_, lean_object* v_indName_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
lean_inc(v_indName_2304_);
v___x_2310_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
if (lean_obj_tag(v_a_2311_) == 5)
{
lean_object* v_val_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2502_; 
v_val_2312_ = lean_ctor_get(v_a_2311_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2311_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2314_ = v_a_2311_;
v_isShared_2315_ = v_isSharedCheck_2502_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_val_2312_);
lean_dec(v_a_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2502_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_inc(v_indName_2304_);
v___x_2316_ = l_Lean_mkCasesOnName(v_indName_2304_);
lean_inc(v___x_2316_);
v___x_2317_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2316_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_name_2319_; lean_object* v_levelParams_2320_; lean_object* v_type_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref(v___x_2317_);
v_name_2319_ = lean_ctor_get(v_a_2318_, 0);
lean_inc(v_name_2319_);
v_levelParams_2320_ = lean_ctor_get(v_a_2318_, 1);
lean_inc_n(v_levelParams_2320_, 2);
v_type_2321_ = lean_ctor_get(v_a_2318_, 2);
lean_inc_ref(v_type_2321_);
lean_dec(v_a_2318_);
v___x_2322_ = lean_box(0);
v___x_2323_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2320_, v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 1)
{
lean_object* v_head_2324_; lean_object* v_tail_2325_; lean_object* v_numParams_2326_; lean_object* v_numIndices_2327_; lean_object* v_ctors_2328_; lean_object* v___f_2329_; lean_object* v___x_2331_; 
v_head_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_head_2324_);
v_tail_2325_ = lean_ctor_get(v___x_2323_, 1);
lean_inc(v_tail_2325_);
v_numParams_2326_ = lean_ctor_get(v_val_2312_, 1);
lean_inc_n(v_numParams_2326_, 2);
v_numIndices_2327_ = lean_ctor_get(v_val_2312_, 2);
lean_inc(v_numIndices_2327_);
v_ctors_2328_ = lean_ctor_get(v_val_2312_, 4);
lean_inc(v_ctors_2328_);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2329_, 0, v_numIndices_2327_);
lean_closure_set(v___f_2329_, 1, v_head_2324_);
lean_closure_set(v___f_2329_, 2, v_ctors_2328_);
lean_closure_set(v___f_2329_, 3, v_tail_2325_);
lean_closure_set(v___f_2329_, 4, v_numParams_2326_);
lean_closure_set(v___f_2329_, 5, v_indName_2304_);
lean_closure_set(v___f_2329_, 6, v_val_2312_);
lean_closure_set(v___f_2329_, 7, v___x_2323_);
lean_closure_set(v___f_2329_, 8, v___x_2316_);
lean_closure_set(v___f_2329_, 9, v_name_2319_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 1);
lean_ctor_set(v___x_2314_, 0, v_numParams_2326_);
v___x_2331_ = v___x_2314_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_numParams_2326_);
v___x_2331_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
uint8_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = 0;
v___x_2333_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2321_, v___x_2331_, v___f_2329_, v___x_2332_, v___x_2332_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; lean_object* v___f_2336_; uint8_t v___y_2338_; uint8_t v___x_2481_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = lean_box(v___x_2332_);
lean_inc(v_declName_2303_);
v___f_2336_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2336_, 0, v_a_2334_);
lean_closure_set(v___f_2336_, 1, v_declName_2303_);
lean_closure_set(v___f_2336_, 2, v_levelParams_2320_);
lean_closure_set(v___f_2336_, 3, v___x_2335_);
v___x_2481_ = l_Lean_isPrivateName(v_declName_2303_);
if (v___x_2481_ == 0)
{
uint8_t v___x_2482_; 
v___x_2482_ = 1;
v___y_2338_ = v___x_2482_;
goto v___jp_2337_;
}
else
{
v___y_2338_ = v___x_2332_;
goto v___jp_2337_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2336_, v___y_2338_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; lean_object* v_env_2341_; lean_object* v_nextMacroScope_2342_; lean_object* v_ngen_2343_; lean_object* v_auxDeclNGen_2344_; lean_object* v_traceState_2345_; lean_object* v_messages_2346_; lean_object* v_infoState_2347_; lean_object* v_snapshotTasks_2348_; lean_object* v_newDecls_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v___x_2339_);
v___x_2340_ = lean_st_ref_take(v_a_2308_);
v_env_2341_ = lean_ctor_get(v___x_2340_, 0);
v_nextMacroScope_2342_ = lean_ctor_get(v___x_2340_, 1);
v_ngen_2343_ = lean_ctor_get(v___x_2340_, 2);
v_auxDeclNGen_2344_ = lean_ctor_get(v___x_2340_, 3);
v_traceState_2345_ = lean_ctor_get(v___x_2340_, 4);
v_messages_2346_ = lean_ctor_get(v___x_2340_, 6);
v_infoState_2347_ = lean_ctor_get(v___x_2340_, 7);
v_snapshotTasks_2348_ = lean_ctor_get(v___x_2340_, 8);
v_newDecls_2349_ = lean_ctor_get(v___x_2340_, 9);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2340_, 5);
lean_dec(v_unused_2480_);
v___x_2351_ = v___x_2340_;
v_isShared_2352_ = v_isSharedCheck_2479_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_newDecls_2349_);
lean_inc(v_snapshotTasks_2348_);
lean_inc(v_infoState_2347_);
lean_inc(v_messages_2346_);
lean_inc(v_traceState_2345_);
lean_inc(v_auxDeclNGen_2344_);
lean_inc(v_ngen_2343_);
lean_inc(v_nextMacroScope_2342_);
lean_inc(v_env_2341_);
lean_dec(v___x_2340_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2479_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_inc(v_declName_2303_);
v___x_2353_ = l_Lean_Meta_markMatcherLike(v_env_2341_, v_declName_2303_);
v___x_2354_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 5, v___x_2354_);
lean_ctor_set(v___x_2351_, 0, v___x_2353_);
v___x_2356_ = v___x_2351_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2342_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2343_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2344_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_traceState_2345_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_messages_2346_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_infoState_2347_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_snapshotTasks_2348_);
lean_ctor_set(v_reuseFailAlloc_2478_, 9, v_newDecls_2349_);
v___x_2356_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_mctx_2359_; lean_object* v_zetaDeltaFVarIds_2360_; lean_object* v_postponed_2361_; lean_object* v_diag_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2476_; 
v___x_2357_ = lean_st_ref_set(v_a_2308_, v___x_2356_);
v___x_2358_ = lean_st_ref_take(v_a_2306_);
v_mctx_2359_ = lean_ctor_get(v___x_2358_, 0);
v_zetaDeltaFVarIds_2360_ = lean_ctor_get(v___x_2358_, 2);
v_postponed_2361_ = lean_ctor_get(v___x_2358_, 3);
v_diag_2362_ = lean_ctor_get(v___x_2358_, 4);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2358_, 1);
lean_dec(v_unused_2477_);
v___x_2364_ = v___x_2358_;
v_isShared_2365_ = v_isSharedCheck_2476_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_diag_2362_);
lean_inc(v_postponed_2361_);
lean_inc(v_zetaDeltaFVarIds_2360_);
lean_inc(v_mctx_2359_);
lean_dec(v___x_2358_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2476_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_mctx_2359_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_zetaDeltaFVarIds_2360_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_postponed_2361_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_diag_2362_);
v___x_2368_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_env_2371_; lean_object* v_nextMacroScope_2372_; lean_object* v_ngen_2373_; lean_object* v_auxDeclNGen_2374_; lean_object* v_traceState_2375_; lean_object* v_messages_2376_; lean_object* v_infoState_2377_; lean_object* v_snapshotTasks_2378_; lean_object* v_newDecls_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2473_; 
v___x_2369_ = lean_st_ref_set(v_a_2306_, v___x_2368_);
v___x_2370_ = lean_st_ref_take(v_a_2308_);
v_env_2371_ = lean_ctor_get(v___x_2370_, 0);
v_nextMacroScope_2372_ = lean_ctor_get(v___x_2370_, 1);
v_ngen_2373_ = lean_ctor_get(v___x_2370_, 2);
v_auxDeclNGen_2374_ = lean_ctor_get(v___x_2370_, 3);
v_traceState_2375_ = lean_ctor_get(v___x_2370_, 4);
v_messages_2376_ = lean_ctor_get(v___x_2370_, 6);
v_infoState_2377_ = lean_ctor_get(v___x_2370_, 7);
v_snapshotTasks_2378_ = lean_ctor_get(v___x_2370_, 8);
v_newDecls_2379_ = lean_ctor_get(v___x_2370_, 9);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2370_, 5);
lean_dec(v_unused_2474_);
v___x_2381_ = v___x_2370_;
v_isShared_2382_ = v_isSharedCheck_2473_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_newDecls_2379_);
lean_inc(v_snapshotTasks_2378_);
lean_inc(v_infoState_2377_);
lean_inc(v_messages_2376_);
lean_inc(v_traceState_2375_);
lean_inc(v_auxDeclNGen_2374_);
lean_inc(v_ngen_2373_);
lean_inc(v_nextMacroScope_2372_);
lean_inc(v_env_2371_);
lean_dec(v___x_2370_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2473_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_inc(v_declName_2303_);
v___x_2383_ = l_Lean_markAuxRecursor(v_env_2371_, v_declName_2303_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 5, v___x_2354_);
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_nextMacroScope_2372_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_ngen_2373_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_auxDeclNGen_2374_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_traceState_2375_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_messages_2376_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_infoState_2377_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_snapshotTasks_2378_);
lean_ctor_set(v_reuseFailAlloc_2472_, 9, v_newDecls_2379_);
v___x_2385_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_mctx_2388_; lean_object* v_zetaDeltaFVarIds_2389_; lean_object* v_postponed_2390_; lean_object* v_diag_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2470_; 
v___x_2386_ = lean_st_ref_set(v_a_2308_, v___x_2385_);
v___x_2387_ = lean_st_ref_take(v_a_2306_);
v_mctx_2388_ = lean_ctor_get(v___x_2387_, 0);
v_zetaDeltaFVarIds_2389_ = lean_ctor_get(v___x_2387_, 2);
v_postponed_2390_ = lean_ctor_get(v___x_2387_, 3);
v_diag_2391_ = lean_ctor_get(v___x_2387_, 4);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2387_, 1);
lean_dec(v_unused_2471_);
v___x_2393_ = v___x_2387_;
v_isShared_2394_ = v_isSharedCheck_2470_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_diag_2391_);
lean_inc(v_postponed_2390_);
lean_inc(v_zetaDeltaFVarIds_2389_);
lean_inc(v_mctx_2388_);
lean_dec(v___x_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2470_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2366_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_mctx_2388_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_zetaDeltaFVarIds_2389_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_postponed_2390_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_diag_2391_);
v___x_2396_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v_nextMacroScope_2400_; lean_object* v_ngen_2401_; lean_object* v_auxDeclNGen_2402_; lean_object* v_traceState_2403_; lean_object* v_messages_2404_; lean_object* v_infoState_2405_; lean_object* v_snapshotTasks_2406_; lean_object* v_newDecls_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2467_; 
v___x_2397_ = lean_st_ref_set(v_a_2306_, v___x_2396_);
v___x_2398_ = lean_st_ref_take(v_a_2308_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
v_nextMacroScope_2400_ = lean_ctor_get(v___x_2398_, 1);
v_ngen_2401_ = lean_ctor_get(v___x_2398_, 2);
v_auxDeclNGen_2402_ = lean_ctor_get(v___x_2398_, 3);
v_traceState_2403_ = lean_ctor_get(v___x_2398_, 4);
v_messages_2404_ = lean_ctor_get(v___x_2398_, 6);
v_infoState_2405_ = lean_ctor_get(v___x_2398_, 7);
v_snapshotTasks_2406_ = lean_ctor_get(v___x_2398_, 8);
v_newDecls_2407_ = lean_ctor_get(v___x_2398_, 9);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2398_, 5);
lean_dec(v_unused_2468_);
v___x_2409_ = v___x_2398_;
v_isShared_2410_ = v_isSharedCheck_2467_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_newDecls_2407_);
lean_inc(v_snapshotTasks_2406_);
lean_inc(v_infoState_2405_);
lean_inc(v_messages_2404_);
lean_inc(v_traceState_2403_);
lean_inc(v_auxDeclNGen_2402_);
lean_inc(v_ngen_2401_);
lean_inc(v_nextMacroScope_2400_);
lean_inc(v_env_2399_);
lean_dec(v___x_2398_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2467_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_inc(v_declName_2303_);
v___x_2411_ = l_Lean_Meta_addToCompletionBlackList(v_env_2399_, v_declName_2303_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 5, v___x_2354_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_nextMacroScope_2400_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_ngen_2401_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_auxDeclNGen_2402_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_traceState_2403_);
lean_ctor_set(v_reuseFailAlloc_2466_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2466_, 6, v_messages_2404_);
lean_ctor_set(v_reuseFailAlloc_2466_, 7, v_infoState_2405_);
lean_ctor_set(v_reuseFailAlloc_2466_, 8, v_snapshotTasks_2406_);
lean_ctor_set(v_reuseFailAlloc_2466_, 9, v_newDecls_2407_);
v___x_2413_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_mctx_2416_; lean_object* v_zetaDeltaFVarIds_2417_; lean_object* v_postponed_2418_; lean_object* v_diag_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2464_; 
v___x_2414_ = lean_st_ref_set(v_a_2308_, v___x_2413_);
v___x_2415_ = lean_st_ref_take(v_a_2306_);
v_mctx_2416_ = lean_ctor_get(v___x_2415_, 0);
v_zetaDeltaFVarIds_2417_ = lean_ctor_get(v___x_2415_, 2);
v_postponed_2418_ = lean_ctor_get(v___x_2415_, 3);
v_diag_2419_ = lean_ctor_get(v___x_2415_, 4);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2415_, 1);
lean_dec(v_unused_2465_);
v___x_2421_ = v___x_2415_;
v_isShared_2422_ = v_isSharedCheck_2464_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_diag_2419_);
lean_inc(v_postponed_2418_);
lean_inc(v_zetaDeltaFVarIds_2417_);
lean_inc(v_mctx_2416_);
lean_dec(v___x_2415_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2464_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___x_2366_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_mctx_2416_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_zetaDeltaFVarIds_2417_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_postponed_2418_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_diag_2419_);
v___x_2424_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_env_2427_; lean_object* v_nextMacroScope_2428_; lean_object* v_ngen_2429_; lean_object* v_auxDeclNGen_2430_; lean_object* v_traceState_2431_; lean_object* v_messages_2432_; lean_object* v_infoState_2433_; lean_object* v_snapshotTasks_2434_; lean_object* v_newDecls_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2461_; 
v___x_2425_ = lean_st_ref_set(v_a_2306_, v___x_2424_);
v___x_2426_ = lean_st_ref_take(v_a_2308_);
v_env_2427_ = lean_ctor_get(v___x_2426_, 0);
v_nextMacroScope_2428_ = lean_ctor_get(v___x_2426_, 1);
v_ngen_2429_ = lean_ctor_get(v___x_2426_, 2);
v_auxDeclNGen_2430_ = lean_ctor_get(v___x_2426_, 3);
v_traceState_2431_ = lean_ctor_get(v___x_2426_, 4);
v_messages_2432_ = lean_ctor_get(v___x_2426_, 6);
v_infoState_2433_ = lean_ctor_get(v___x_2426_, 7);
v_snapshotTasks_2434_ = lean_ctor_get(v___x_2426_, 8);
v_newDecls_2435_ = lean_ctor_get(v___x_2426_, 9);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2426_, 5);
lean_dec(v_unused_2462_);
v___x_2437_ = v___x_2426_;
v_isShared_2438_ = v_isSharedCheck_2461_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_newDecls_2435_);
lean_inc(v_snapshotTasks_2434_);
lean_inc(v_infoState_2433_);
lean_inc(v_messages_2432_);
lean_inc(v_traceState_2431_);
lean_inc(v_auxDeclNGen_2430_);
lean_inc(v_ngen_2429_);
lean_inc(v_nextMacroScope_2428_);
lean_inc(v_env_2427_);
lean_dec(v___x_2426_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2461_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc(v_declName_2303_);
v___x_2439_ = l_Lean_addProtected(v_env_2427_, v_declName_2303_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 5, v___x_2354_);
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_nextMacroScope_2428_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_ngen_2429_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_auxDeclNGen_2430_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_traceState_2431_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2460_, 6, v_messages_2432_);
lean_ctor_set(v_reuseFailAlloc_2460_, 7, v_infoState_2433_);
lean_ctor_set(v_reuseFailAlloc_2460_, 8, v_snapshotTasks_2434_);
lean_ctor_set(v_reuseFailAlloc_2460_, 9, v_newDecls_2435_);
v___x_2441_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_mctx_2444_; lean_object* v_zetaDeltaFVarIds_2445_; lean_object* v_postponed_2446_; lean_object* v_diag_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2458_; 
v___x_2442_ = lean_st_ref_set(v_a_2308_, v___x_2441_);
v___x_2443_ = lean_st_ref_take(v_a_2306_);
v_mctx_2444_ = lean_ctor_get(v___x_2443_, 0);
v_zetaDeltaFVarIds_2445_ = lean_ctor_get(v___x_2443_, 2);
v_postponed_2446_ = lean_ctor_get(v___x_2443_, 3);
v_diag_2447_ = lean_ctor_get(v___x_2443_, 4);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2443_, 1);
lean_dec(v_unused_2459_);
v___x_2449_ = v___x_2443_;
v_isShared_2450_ = v_isSharedCheck_2458_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_diag_2447_);
lean_inc(v_postponed_2446_);
lean_inc(v_zetaDeltaFVarIds_2445_);
lean_inc(v_mctx_2444_);
lean_dec(v___x_2443_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2458_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v___x_2366_);
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_mctx_2444_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_zetaDeltaFVarIds_2445_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_postponed_2446_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_diag_2447_);
v___x_2452_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_st_ref_set(v_a_2306_, v___x_2452_);
v___x_2454_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2303_);
v___x_2455_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2454_, v_declName_2303_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref(v___x_2455_);
v___x_2456_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2303_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2456_;
}
else
{
lean_dec(v_declName_2303_);
return v___x_2455_;
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
lean_dec(v_declName_2303_);
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_levelParams_2320_);
lean_dec(v_declName_2303_);
v_a_2483_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2333_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2333_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec(v___x_2323_);
lean_dec_ref(v_type_2321_);
lean_dec(v_levelParams_2320_);
lean_dec(v_name_2319_);
lean_dec(v___x_2316_);
lean_del_object(v___x_2314_);
lean_dec_ref(v_val_2312_);
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v___x_2492_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2493_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2492_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2493_;
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v___x_2316_);
lean_del_object(v___x_2314_);
lean_dec_ref(v_val_2312_);
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v_a_2494_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2317_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2317_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_a_2311_);
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v___x_2503_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2504_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2503_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2504_;
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v_a_2505_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2310_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2310_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2513_, lean_object* v_indName_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2513_, v_indName_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2521_, lean_object* v_name_2522_, lean_object* v_type_2523_, lean_object* v_k_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2522_, v_type_2523_, v_k_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2531_, lean_object* v_name_2532_, lean_object* v_type_2533_, lean_object* v_k_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2531_, v_name_2532_, v_type_2533_, v_k_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2541_, lean_object* v_params_2542_, lean_object* v_alts_2543_, lean_object* v___x_2544_, lean_object* v_ism2_2545_, lean_object* v_motive_2546_, lean_object* v_val_2547_, lean_object* v_indName_2548_, lean_object* v___x_2549_, lean_object* v___x_2550_, lean_object* v___x_2551_, lean_object* v_as_2552_, lean_object* v_i_2553_, lean_object* v_j_2554_, lean_object* v_inv_2555_, lean_object* v_bs_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2541_, v_params_2542_, v_alts_2543_, v___x_2544_, v_ism2_2545_, v_motive_2546_, v_val_2547_, v_indName_2548_, v___x_2549_, v___x_2550_, v___x_2551_, v_as_2552_, v_i_2553_, v_j_2554_, v_bs_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2563_ = _args[0];
lean_object* v_params_2564_ = _args[1];
lean_object* v_alts_2565_ = _args[2];
lean_object* v___x_2566_ = _args[3];
lean_object* v_ism2_2567_ = _args[4];
lean_object* v_motive_2568_ = _args[5];
lean_object* v_val_2569_ = _args[6];
lean_object* v_indName_2570_ = _args[7];
lean_object* v___x_2571_ = _args[8];
lean_object* v___x_2572_ = _args[9];
lean_object* v___x_2573_ = _args[10];
lean_object* v_as_2574_ = _args[11];
lean_object* v_i_2575_ = _args[12];
lean_object* v_j_2576_ = _args[13];
lean_object* v_inv_2577_ = _args[14];
lean_object* v_bs_2578_ = _args[15];
lean_object* v___y_2579_ = _args[16];
lean_object* v___y_2580_ = _args[17];
lean_object* v___y_2581_ = _args[18];
lean_object* v___y_2582_ = _args[19];
lean_object* v___y_2583_ = _args[20];
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2563_, v_params_2564_, v_alts_2565_, v___x_2566_, v_ism2_2567_, v_motive_2568_, v_val_2569_, v_indName_2570_, v___x_2571_, v___x_2572_, v___x_2573_, v_as_2574_, v_i_2575_, v_j_2576_, v_inv_2577_, v_bs_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v_as_2574_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2585_, lean_object* v_params_2586_, lean_object* v___x_2587_, lean_object* v_motive_2588_, lean_object* v_as_2589_, lean_object* v_i_2590_, lean_object* v_j_2591_, lean_object* v_inv_2592_, lean_object* v_bs_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2585_, v_params_2586_, v___x_2587_, v_motive_2588_, v_as_2589_, v_i_2590_, v_j_2591_, v_bs_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2600_, lean_object* v_params_2601_, lean_object* v___x_2602_, lean_object* v_motive_2603_, lean_object* v_as_2604_, lean_object* v_i_2605_, lean_object* v_j_2606_, lean_object* v_inv_2607_, lean_object* v_bs_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2600_, v_params_2601_, v___x_2602_, v_motive_2603_, v_as_2604_, v_i_2605_, v_j_2606_, v_inv_2607_, v_bs_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v_as_2604_);
lean_dec_ref(v_params_2601_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2615_, uint8_t v_s_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2615_, v_s_2616_, v___y_2618_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2623_, lean_object* v_s_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v_s_boxed_2630_; lean_object* v_res_2631_; 
v_s_boxed_2630_ = lean_unbox(v_s_2624_);
v_res_2631_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2623_, v_s_boxed_2630_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2632_, lean_object* v_constName_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_constName_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2640_, v_constName_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2648_, lean_object* v_attrName_2649_, lean_object* v_declName_2650_, lean_object* v_asyncPrefix_x3f_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2649_, v_declName_2650_, v_asyncPrefix_x3f_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2658_, lean_object* v_attrName_2659_, lean_object* v_declName_2660_, lean_object* v_asyncPrefix_x3f_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2658_, v_attrName_2659_, v_declName_2660_, v_asyncPrefix_x3f_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2668_, lean_object* v_attrName_2669_, lean_object* v_declName_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2669_, v_declName_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_attrName_2678_, lean_object* v_declName_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2677_, v_attrName_2678_, v_declName_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2686_, lean_object* v_ref_2687_, lean_object* v_constName_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2687_, v_constName_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2695_, lean_object* v_ref_2696_, lean_object* v_constName_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2695_, v_ref_2696_, v_constName_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v_ref_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2712_, v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, lean_object* v_msg_2722_, lean_object* v_declHint_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2721_, v_msg_2722_, v_declHint_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_ref_2731_, lean_object* v_msg_2732_, lean_object* v_declHint_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2730_, v_ref_2731_, v_msg_2732_, v_declHint_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v_ref_2731_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2740_, lean_object* v_declHint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2740_, v_declHint_2741_, v___y_2745_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2748_, lean_object* v_declHint_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2748_, v_declHint_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2756_, lean_object* v_ref_2757_, lean_object* v_msg_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2757_, v_msg_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_ref_2766_, lean_object* v_msg_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2765_, v_ref_2766_, v_msg_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v_ref_2766_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = l_Lean_Expr_hasMVar(v_e_2774_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v_e_2774_);
return v___x_2778_;
}
else
{
lean_object* v___x_2779_; lean_object* v_mctx_2780_; lean_object* v___x_2781_; lean_object* v_fst_2782_; lean_object* v_snd_2783_; lean_object* v___x_2784_; lean_object* v_cache_2785_; lean_object* v_zetaDeltaFVarIds_2786_; lean_object* v_postponed_2787_; lean_object* v_diag_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2797_; 
v___x_2779_ = lean_st_ref_get(v___y_2775_);
v_mctx_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_ref(v_mctx_2780_);
lean_dec(v___x_2779_);
v___x_2781_ = l_Lean_instantiateMVarsCore(v_mctx_2780_, v_e_2774_);
v_fst_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_fst_2782_);
v_snd_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_snd_2783_);
lean_dec_ref(v___x_2781_);
v___x_2784_ = lean_st_ref_take(v___y_2775_);
v_cache_2785_ = lean_ctor_get(v___x_2784_, 1);
v_zetaDeltaFVarIds_2786_ = lean_ctor_get(v___x_2784_, 2);
v_postponed_2787_ = lean_ctor_get(v___x_2784_, 3);
v_diag_2788_ = lean_ctor_get(v___x_2784_, 4);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2784_, 0);
lean_dec(v_unused_2798_);
v___x_2790_ = v___x_2784_;
v_isShared_2791_ = v_isSharedCheck_2797_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_diag_2788_);
lean_inc(v_postponed_2787_);
lean_inc(v_zetaDeltaFVarIds_2786_);
lean_inc(v_cache_2785_);
lean_dec(v___x_2784_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2797_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_snd_2783_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_snd_2783_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_cache_2785_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_zetaDeltaFVarIds_2786_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_postponed_2787_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_diag_2788_);
v___x_2793_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_st_ref_set(v___y_2775_, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_fst_2782_);
return v___x_2795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2799_, v___y_2800_);
lean_dec(v___y_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2803_, v___y_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2817_, lean_object* v_info_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v_nextMacroScope_2824_; lean_object* v_ngen_2825_; lean_object* v_auxDeclNGen_2826_; lean_object* v_traceState_2827_; lean_object* v_messages_2828_; lean_object* v_infoState_2829_; lean_object* v_snapshotTasks_2830_; lean_object* v_newDecls_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2858_; 
v___x_2822_ = lean_st_ref_take(v___y_2820_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
v_nextMacroScope_2824_ = lean_ctor_get(v___x_2822_, 1);
v_ngen_2825_ = lean_ctor_get(v___x_2822_, 2);
v_auxDeclNGen_2826_ = lean_ctor_get(v___x_2822_, 3);
v_traceState_2827_ = lean_ctor_get(v___x_2822_, 4);
v_messages_2828_ = lean_ctor_get(v___x_2822_, 6);
v_infoState_2829_ = lean_ctor_get(v___x_2822_, 7);
v_snapshotTasks_2830_ = lean_ctor_get(v___x_2822_, 8);
v_newDecls_2831_ = lean_ctor_get(v___x_2822_, 9);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2822_, 5);
lean_dec(v_unused_2859_);
v___x_2833_ = v___x_2822_;
v_isShared_2834_ = v_isSharedCheck_2858_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_newDecls_2831_);
lean_inc(v_snapshotTasks_2830_);
lean_inc(v_infoState_2829_);
lean_inc(v_messages_2828_);
lean_inc(v_traceState_2827_);
lean_inc(v_auxDeclNGen_2826_);
lean_inc(v_ngen_2825_);
lean_inc(v_nextMacroScope_2824_);
lean_inc(v_env_2823_);
lean_dec(v___x_2822_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2858_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2835_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2823_, v_matcherName_2817_, v_info_2818_);
v___x_2836_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 5, v___x_2836_);
lean_ctor_set(v___x_2833_, 0, v___x_2835_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_nextMacroScope_2824_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_ngen_2825_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_auxDeclNGen_2826_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_traceState_2827_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_messages_2828_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_infoState_2829_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_snapshotTasks_2830_);
lean_ctor_set(v_reuseFailAlloc_2857_, 9, v_newDecls_2831_);
v___x_2838_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_mctx_2841_; lean_object* v_zetaDeltaFVarIds_2842_; lean_object* v_postponed_2843_; lean_object* v_diag_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2855_; 
v___x_2839_ = lean_st_ref_set(v___y_2820_, v___x_2838_);
v___x_2840_ = lean_st_ref_take(v___y_2819_);
v_mctx_2841_ = lean_ctor_get(v___x_2840_, 0);
v_zetaDeltaFVarIds_2842_ = lean_ctor_get(v___x_2840_, 2);
v_postponed_2843_ = lean_ctor_get(v___x_2840_, 3);
v_diag_2844_ = lean_ctor_get(v___x_2840_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2840_, 1);
lean_dec(v_unused_2856_);
v___x_2846_ = v___x_2840_;
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_diag_2844_);
lean_inc(v_postponed_2843_);
lean_inc(v_zetaDeltaFVarIds_2842_);
lean_inc(v_mctx_2841_);
lean_dec(v___x_2840_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 1, v___x_2848_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_mctx_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_zetaDeltaFVarIds_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_postponed_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_diag_2844_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_st_ref_set(v___y_2819_, v___x_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2860_, lean_object* v_info_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2860_, v_info_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec(v___y_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2866_, lean_object* v_info_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2866_, v_info_2867_, v___y_2869_, v___y_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2874_, lean_object* v_info_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2874_, v_info_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2882_, lean_object* v___x_2883_, lean_object* v_newEqs1_2884_, uint8_t v___x_2885_, uint8_t v___x_2886_, uint8_t v___x_2887_, lean_object* v_ism1_x27_2888_, lean_object* v_ism2_x27_2889_, lean_object* v_newRefls1_2890_, lean_object* v_newEqs2_2891_, lean_object* v_newRefls2_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = l_Lean_mkAppN(v_motive_2882_, v___x_2883_);
v___x_2899_ = l_Array_append___redArg(v_newEqs1_2884_, v_newEqs2_2891_);
v___x_2900_ = l_Lean_Meta_mkForallFVars(v___x_2899_, v___x_2898_, v___x_2885_, v___x_2886_, v___x_2886_, v___x_2887_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec_ref(v___x_2899_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = l_Array_append___redArg(v_ism1_x27_2888_, v_ism2_x27_2889_);
v___x_2903_ = l_Lean_Meta_mkLambdaFVars(v___x_2902_, v_a_2901_, v___x_2885_, v___x_2886_, v___x_2885_, v___x_2886_, v___x_2887_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec_ref(v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2913_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2908_ = l_Array_append___redArg(v_newRefls1_2890_, v_newRefls2_2892_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_a_2904_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_newRefls1_2890_);
v_a_2914_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2903_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2903_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v_newRefls1_2890_);
lean_dec_ref(v_ism1_x27_2888_);
v_a_2922_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2900_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2900_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2930_, lean_object* v___x_2931_, lean_object* v_newEqs1_2932_, lean_object* v___x_2933_, lean_object* v___x_2934_, lean_object* v___x_2935_, lean_object* v_ism1_x27_2936_, lean_object* v_ism2_x27_2937_, lean_object* v_newRefls1_2938_, lean_object* v_newEqs2_2939_, lean_object* v_newRefls2_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v___x_15224__boxed_2946_; uint8_t v___x_15225__boxed_2947_; uint8_t v___x_15226__boxed_2948_; lean_object* v_res_2949_; 
v___x_15224__boxed_2946_ = lean_unbox(v___x_2933_);
v___x_15225__boxed_2947_ = lean_unbox(v___x_2934_);
v___x_15226__boxed_2948_ = lean_unbox(v___x_2935_);
v_res_2949_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2930_, v___x_2931_, v_newEqs1_2932_, v___x_15224__boxed_2946_, v___x_15225__boxed_2947_, v___x_15226__boxed_2948_, v_ism1_x27_2936_, v_ism2_x27_2937_, v_newRefls1_2938_, v_newEqs2_2939_, v_newRefls2_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec_ref(v_newRefls2_2940_);
lean_dec_ref(v_newEqs2_2939_);
lean_dec_ref(v_ism2_x27_2937_);
lean_dec_ref(v___x_2931_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2950_, lean_object* v___x_2951_, uint8_t v___x_2952_, uint8_t v___x_2953_, uint8_t v___x_2954_, lean_object* v_ism1_x27_2955_, lean_object* v_ism2_x27_2956_, lean_object* v_is_2957_, lean_object* v___x_2958_, lean_object* v_newEqs1_2959_, lean_object* v_newRefls1_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2966_ = lean_box(v___x_2952_);
v___x_2967_ = lean_box(v___x_2953_);
v___x_2968_ = lean_box(v___x_2954_);
lean_inc_ref(v_ism2_x27_2956_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2969_, 0, v_motive_2950_);
lean_closure_set(v___f_2969_, 1, v___x_2951_);
lean_closure_set(v___f_2969_, 2, v_newEqs1_2959_);
lean_closure_set(v___f_2969_, 3, v___x_2966_);
lean_closure_set(v___f_2969_, 4, v___x_2967_);
lean_closure_set(v___f_2969_, 5, v___x_2968_);
lean_closure_set(v___f_2969_, 6, v_ism1_x27_2955_);
lean_closure_set(v___f_2969_, 7, v_ism2_x27_2956_);
lean_closure_set(v___f_2969_, 8, v_newRefls1_2960_);
v___x_2970_ = lean_array_push(v_is_2957_, v___x_2958_);
v___x_2971_ = l_Lean_Meta_withNewEqs___redArg(v___x_2970_, v_ism2_x27_2956_, v___f_2969_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2972_, lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v___x_2976_, lean_object* v_ism1_x27_2977_, lean_object* v_ism2_x27_2978_, lean_object* v_is_2979_, lean_object* v___x_2980_, lean_object* v_newEqs1_2981_, lean_object* v_newRefls1_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v___x_15315__boxed_2988_; uint8_t v___x_15316__boxed_2989_; uint8_t v___x_15317__boxed_2990_; lean_object* v_res_2991_; 
v___x_15315__boxed_2988_ = lean_unbox(v___x_2974_);
v___x_15316__boxed_2989_ = lean_unbox(v___x_2975_);
v___x_15317__boxed_2990_ = lean_unbox(v___x_2976_);
v_res_2991_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2972_, v___x_2973_, v___x_15315__boxed_2988_, v___x_15316__boxed_2989_, v___x_15317__boxed_2990_, v_ism1_x27_2977_, v_ism2_x27_2978_, v_is_2979_, v___x_2980_, v_newEqs1_2981_, v_newRefls1_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2992_, uint8_t v___x_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_addDecl(v___x_2992_, v___x_2993_, v___y_2996_, v___y_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
uint8_t v___x_15357__boxed_3007_; lean_object* v_res_3008_; 
v___x_15357__boxed_3007_ = lean_unbox(v___x_3001_);
v_res_3008_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3000_, v___x_15357__boxed_3007_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3008_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3011_ = l_Lean_stringToMessageData(v___x_3010_);
return v___x_3011_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3014_ = l_Lean_stringToMessageData(v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_box(0);
v___x_3021_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3022_ = l_Lean_mkConst(v___x_3021_, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3025_ = l_Lean_stringToMessageData(v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3026_, lean_object* v_a_3027_, lean_object* v_j_3028_, lean_object* v_zs1_3029_, lean_object* v_snd_3030_, uint8_t v___x_3031_, uint8_t v_isZero_3032_, uint8_t v___x_3033_, lean_object* v_alts_3034_, lean_object* v_zs2_3035_, lean_object* v___ctorRet2_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_array_get_borrowed(v___x_3026_, v_a_3027_, v_j_3028_);
lean_inc_ref(v_zs1_3029_);
v___x_3043_ = l_Array_append___redArg(v_zs1_3029_, v_zs2_3035_);
lean_inc(v___x_3042_);
v___x_3044_ = l_Lean_Meta_instantiateForall(v___x_3042_, v___x_3043_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3044_);
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3045_, v___x_3046_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = l_Lean_Expr_mvarId_x21(v_a_3048_);
v___x_3050_ = lean_array_get_size(v_snd_3030_);
v___x_3051_ = lean_box(0);
v___x_3052_ = lean_box(0);
lean_inc_ref(v___y_3039_);
v___x_3053_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3050_, v___x_3049_, v___x_3051_, v___x_3052_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
if (lean_obj_tag(v_a_3054_) == 1)
{
lean_object* v_val_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3102_; 
v_val_3055_ = lean_ctor_get(v_a_3054_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3054_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3057_ = v_a_3054_;
v_isShared_3058_ = v_isSharedCheck_3102_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_val_3055_);
lean_dec(v_a_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3102_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v_fst_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3100_; 
v_fst_3059_ = lean_ctor_get(v_val_3055_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_val_3055_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v_val_3055_, 1);
lean_dec(v_unused_3101_);
v___x_3061_ = v_val_3055_;
v_isShared_3062_ = v_isSharedCheck_3100_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_fst_3059_);
lean_dec(v_val_3055_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3100_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___y_3064_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3092_ = lean_array_get_borrowed(v___x_3026_, v_alts_3034_, v_j_3028_);
v___x_3093_ = lean_array_get_size(v_zs1_3029_);
lean_dec_ref(v_zs1_3029_);
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_nat_dec_eq(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_inc(v___x_3092_);
v___y_3064_ = v___x_3092_;
goto v___jp_3063_;
}
else
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = lean_array_get_size(v_zs2_3035_);
v___x_3097_ = lean_nat_dec_eq(v___x_3096_, v___x_3094_);
if (v___x_3097_ == 0)
{
lean_inc(v___x_3092_);
v___y_3064_ = v___x_3092_;
goto v___jp_3063_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3092_);
v___x_3099_ = l_Lean_Expr_app___override(v___x_3092_, v___x_3098_);
v___y_3064_ = v___x_3099_;
goto v___jp_3063_;
}
}
v___jp_3063_:
{
uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = 0;
v___x_3066_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3066_, 0, v___x_3065_);
lean_ctor_set_uint8(v___x_3066_, 1, v___x_3031_);
lean_ctor_set_uint8(v___x_3066_, 2, v_isZero_3032_);
lean_ctor_set_uint8(v___x_3066_, 3, v___x_3031_);
lean_inc_ref(v___y_3064_);
lean_inc(v_fst_3059_);
v___x_3067_ = l_Lean_MVarId_apply(v_fst_3059_, v___y_3064_, v___x_3066_, v___x_3052_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
if (lean_obj_tag(v_a_3068_) == 0)
{
lean_object* v___x_3069_; lean_object* v_a_3070_; lean_object* v___x_3071_; 
lean_dec_ref(v___y_3064_);
lean_del_object(v___x_3061_);
lean_dec(v_fst_3059_);
lean_del_object(v___x_3057_);
v___x_3069_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3048_, v___y_3038_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref(v___x_3069_);
v___x_3071_ = l_Lean_Meta_mkLambdaFVars(v___x_3043_, v_a_3070_, v_isZero_3032_, v___x_3031_, v_isZero_3032_, v___x_3031_, v___x_3033_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec_ref(v___x_3043_);
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_dec(v_a_3068_);
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
v___x_3072_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3073_ = l_Lean_MessageData_ofExpr(v___y_3064_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 7);
lean_ctor_set(v___x_3061_, 1, v___x_3073_);
lean_ctor_set(v___x_3061_, 0, v___x_3072_);
v___x_3075_ = v___x_3061_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3076_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v_fst_3059_);
v___x_3079_ = v___x_3057_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_fst_3059_);
v___x_3079_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3077_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3080_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v___y_3064_);
lean_del_object(v___x_3061_);
lean_dec(v_fst_3059_);
lean_del_object(v___x_3057_);
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
v_a_3084_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3067_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3067_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_a_3054_);
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
v___x_3103_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3104_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3103_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3104_;
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
v_a_3105_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3053_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3053_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
return v___x_3047_;
}
}
else
{
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3113_, lean_object* v_a_3114_, lean_object* v_j_3115_, lean_object* v_zs1_3116_, lean_object* v_snd_3117_, lean_object* v___x_3118_, lean_object* v_isZero_3119_, lean_object* v___x_3120_, lean_object* v_alts_3121_, lean_object* v_zs2_3122_, lean_object* v___ctorRet2_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_15416__boxed_3129_; uint8_t v_isZero_boxed_3130_; uint8_t v___x_15417__boxed_3131_; lean_object* v_res_3132_; 
v___x_15416__boxed_3129_ = lean_unbox(v___x_3118_);
v_isZero_boxed_3130_ = lean_unbox(v_isZero_3119_);
v___x_15417__boxed_3131_ = lean_unbox(v___x_3120_);
v_res_3132_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3113_, v_a_3114_, v_j_3115_, v_zs1_3116_, v_snd_3117_, v___x_15416__boxed_3129_, v_isZero_boxed_3130_, v___x_15417__boxed_3131_, v_alts_3121_, v_zs2_3122_, v___ctorRet2_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v___ctorRet2_3123_);
lean_dec_ref(v_zs2_3122_);
lean_dec_ref(v_alts_3121_);
lean_dec_ref(v_snd_3117_);
lean_dec(v_j_3115_);
lean_dec_ref(v_a_3114_);
lean_dec_ref(v___x_3113_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3133_, lean_object* v_a_3134_, lean_object* v_j_3135_, lean_object* v_snd_3136_, uint8_t v___x_3137_, uint8_t v_isZero_3138_, uint8_t v___x_3139_, lean_object* v_alts_3140_, lean_object* v_a_3141_, lean_object* v_zs1_3142_, lean_object* v___ctorRet1_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; 
v___x_3149_ = lean_box(v___x_3137_);
v___x_3150_ = lean_box(v_isZero_3138_);
v___x_3151_ = lean_box(v___x_3139_);
v___f_3152_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3152_, 0, v___x_3133_);
lean_closure_set(v___f_3152_, 1, v_a_3134_);
lean_closure_set(v___f_3152_, 2, v_j_3135_);
lean_closure_set(v___f_3152_, 3, v_zs1_3142_);
lean_closure_set(v___f_3152_, 4, v_snd_3136_);
lean_closure_set(v___f_3152_, 5, v___x_3149_);
lean_closure_set(v___f_3152_, 6, v___x_3150_);
lean_closure_set(v___f_3152_, 7, v___x_3151_);
lean_closure_set(v___f_3152_, 8, v_alts_3140_);
v___x_3153_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3141_, v___f_3152_, v_isZero_3138_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3154_, lean_object* v_a_3155_, lean_object* v_j_3156_, lean_object* v_snd_3157_, lean_object* v___x_3158_, lean_object* v_isZero_3159_, lean_object* v___x_3160_, lean_object* v_alts_3161_, lean_object* v_a_3162_, lean_object* v_zs1_3163_, lean_object* v___ctorRet1_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v___x_15609__boxed_3170_; uint8_t v_isZero_boxed_3171_; uint8_t v___x_15610__boxed_3172_; lean_object* v_res_3173_; 
v___x_15609__boxed_3170_ = lean_unbox(v___x_3158_);
v_isZero_boxed_3171_ = lean_unbox(v_isZero_3159_);
v___x_15610__boxed_3172_ = lean_unbox(v___x_3160_);
v_res_3173_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3154_, v_a_3155_, v_j_3156_, v_snd_3157_, v___x_15609__boxed_3170_, v_isZero_boxed_3171_, v___x_15610__boxed_3172_, v_alts_3161_, v_a_3162_, v_zs1_3163_, v___ctorRet1_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v___ctorRet1_3164_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3174_, lean_object* v_params_3175_, lean_object* v_a_3176_, lean_object* v_snd_3177_, lean_object* v_alts_3178_, lean_object* v_as_3179_, lean_object* v_i_3180_, lean_object* v_j_3181_, lean_object* v_bs_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_zero_3188_; uint8_t v_isZero_3189_; 
v_zero_3188_ = lean_unsigned_to_nat(0u);
v_isZero_3189_ = lean_nat_dec_eq(v_i_3180_, v_zero_3188_);
if (v_isZero_3189_ == 1)
{
lean_object* v___x_3190_; 
lean_dec(v_j_3181_);
lean_dec(v_i_3180_);
lean_dec_ref(v_alts_3178_);
lean_dec_ref(v_snd_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_tail_3174_);
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_bs_3182_);
return v___x_3190_;
}
else
{
lean_object* v_one_3191_; lean_object* v_n_3192_; lean_object* v___y_3194_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_one_3191_ = lean_unsigned_to_nat(1u);
v_n_3192_ = lean_nat_sub(v_i_3180_, v_one_3191_);
lean_dec(v_i_3180_);
v___x_3207_ = lean_array_fget_borrowed(v_as_3179_, v_j_3181_);
lean_inc(v_tail_3174_);
lean_inc(v___x_3207_);
v___x_3208_ = l_Lean_mkConst(v___x_3207_, v_tail_3174_);
v___x_3209_ = l_Lean_mkAppN(v___x_3208_, v_params_3175_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
v___x_3210_ = lean_infer_type(v___x_3209_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc_n(v_a_3211_, 2);
lean_dec_ref(v___x_3210_);
v___x_3212_ = l_Lean_instInhabitedExpr;
v___x_3213_ = 1;
v___x_3214_ = 1;
v___x_3215_ = lean_box(v___x_3213_);
v___x_3216_ = lean_box(v_isZero_3189_);
v___x_3217_ = lean_box(v___x_3214_);
lean_inc_ref(v_alts_3178_);
lean_inc_ref(v_snd_3177_);
lean_inc(v_j_3181_);
lean_inc_ref(v_a_3176_);
v___f_3218_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3218_, 0, v___x_3212_);
lean_closure_set(v___f_3218_, 1, v_a_3176_);
lean_closure_set(v___f_3218_, 2, v_j_3181_);
lean_closure_set(v___f_3218_, 3, v_snd_3177_);
lean_closure_set(v___f_3218_, 4, v___x_3215_);
lean_closure_set(v___f_3218_, 5, v___x_3216_);
lean_closure_set(v___f_3218_, 6, v___x_3217_);
lean_closure_set(v___f_3218_, 7, v_alts_3178_);
lean_closure_set(v___f_3218_, 8, v_a_3211_);
v___x_3219_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3211_, v___f_3218_, v_isZero_3189_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
v___y_3194_ = v___x_3219_;
goto v___jp_3193_;
}
else
{
v___y_3194_ = v___x_3210_;
goto v___jp_3193_;
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_a_3195_ = lean_ctor_get(v___y_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref(v___y_3194_);
v___x_3196_ = lean_nat_add(v_j_3181_, v_one_3191_);
lean_dec(v_j_3181_);
v___x_3197_ = lean_array_push(v_bs_3182_, v_a_3195_);
v_i_3180_ = v_n_3192_;
v_j_3181_ = v___x_3196_;
v_bs_3182_ = v___x_3197_;
goto _start;
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v_n_3192_);
lean_dec_ref(v_bs_3182_);
lean_dec(v_j_3181_);
lean_dec_ref(v_alts_3178_);
lean_dec_ref(v_snd_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_tail_3174_);
v_a_3199_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___y_3194_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___y_3194_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3220_, lean_object* v_params_3221_, lean_object* v_a_3222_, lean_object* v_snd_3223_, lean_object* v_alts_3224_, lean_object* v_as_3225_, lean_object* v_i_3226_, lean_object* v_j_3227_, lean_object* v_bs_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3220_, v_params_3221_, v_a_3222_, v_snd_3223_, v_alts_3224_, v_as_3225_, v_i_3226_, v_j_3227_, v_bs_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v_as_3225_);
lean_dec_ref(v_params_3221_);
return v_res_3234_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_unsigned_to_nat(16u);
v___x_3237_ = lean_mk_array(v___x_3236_, v___x_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3238_, lean_object* v___x_3239_, uint8_t v___x_3240_, uint8_t v___x_3241_, uint8_t v___x_3242_, lean_object* v_ism1_x27_3243_, lean_object* v_is_3244_, lean_object* v___x_3245_, lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v_params_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v_heq_3252_, lean_object* v_val_3253_, lean_object* v___x_3254_, lean_object* v_tail_3255_, lean_object* v_alts_3256_, lean_object* v___x_3257_, lean_object* v___x_3258_, lean_object* v___x_3259_, lean_object* v_declName_3260_, lean_object* v_levelParams_3261_, lean_object* v_numIndices_3262_, lean_object* v___x_3263_, lean_object* v_numParams_3264_, lean_object* v_snd_3265_, lean_object* v_ism2_x27_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___f_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3273_ = lean_box(v___x_3240_);
v___x_3274_ = lean_box(v___x_3241_);
v___x_3275_ = lean_box(v___x_3242_);
lean_inc_ref(v___x_3245_);
lean_inc_ref_n(v_is_3244_, 2);
lean_inc_ref(v_ism1_x27_3243_);
lean_inc_ref(v_motive_3238_);
v___f_3276_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3276_, 0, v_motive_3238_);
lean_closure_set(v___f_3276_, 1, v___x_3239_);
lean_closure_set(v___f_3276_, 2, v___x_3273_);
lean_closure_set(v___f_3276_, 3, v___x_3274_);
lean_closure_set(v___f_3276_, 4, v___x_3275_);
lean_closure_set(v___f_3276_, 5, v_ism1_x27_3243_);
lean_closure_set(v___f_3276_, 6, v_ism2_x27_3266_);
lean_closure_set(v___f_3276_, 7, v_is_3244_);
lean_closure_set(v___f_3276_, 8, v___x_3245_);
lean_inc_ref(v___x_3246_);
v___x_3277_ = lean_array_push(v_is_3244_, v___x_3246_);
v___x_3278_ = l_Lean_Meta_withNewEqs___redArg(v___x_3277_, v_ism1_x27_3243_, v___f_3276_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v_fst_3280_; lean_object* v_snd_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3383_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref(v___x_3278_);
v_fst_3280_ = lean_ctor_get(v_a_3279_, 0);
v_snd_3281_ = lean_ctor_get(v_a_3279_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3279_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3283_ = v_a_3279_;
v_isShared_3284_ = v_isSharedCheck_3383_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_snd_3281_);
lean_inc(v_fst_3280_);
lean_dec(v_a_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3383_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3285_ = l_Lean_mkConst(v___x_3247_, v___x_3248_);
v___x_3286_ = l_Lean_mkAppN(v___x_3285_, v_params_3249_);
v___x_3287_ = l_Lean_Expr_app___override(v___x_3286_, v_fst_3280_);
lean_inc_ref(v_is_3244_);
v___x_3288_ = l_Array_append___redArg(v_is_3244_, v___x_3250_);
v___x_3289_ = l_Array_append___redArg(v___x_3288_, v_is_3244_);
v___x_3290_ = l_Array_append___redArg(v___x_3289_, v___x_3251_);
v___x_3291_ = l_Lean_mkAppN(v___x_3287_, v___x_3290_);
lean_dec_ref(v___x_3290_);
lean_inc_ref(v_heq_3252_);
v___x_3292_ = l_Lean_Expr_app___override(v___x_3291_, v_heq_3252_);
v___x_3293_ = l_Lean_InductiveVal_numCtors(v_val_3253_);
lean_inc_ref(v___x_3292_);
v___x_3294_ = l_Lean_Meta_inferArgumentTypesN(v___x_3293_, v___x_3292_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref(v___x_3294_);
v___x_3296_ = lean_mk_empty_array_with_capacity(v___x_3254_);
lean_inc(v___x_3258_);
lean_inc_ref(v_alts_3256_);
lean_inc(v_snd_3281_);
v___x_3297_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3255_, v_params_3249_, v_a_3295_, v_snd_3281_, v_alts_3256_, v___x_3257_, v___x_3254_, v___x_3258_, v___x_3296_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = l_Lean_mkAppN(v___x_3292_, v_a_3298_);
lean_dec(v_a_3298_);
v___x_3300_ = l_Lean_mkAppN(v___x_3299_, v_snd_3281_);
lean_dec(v_snd_3281_);
lean_inc_ref(v___x_3259_);
v___x_3301_ = lean_array_push(v___x_3259_, v_motive_3238_);
v___x_3302_ = l_Array_append___redArg(v_params_3249_, v___x_3301_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = l_Array_append___redArg(v___x_3302_, v_is_3244_);
lean_dec_ref(v_is_3244_);
v___x_3304_ = lean_unsigned_to_nat(2u);
v___x_3305_ = lean_mk_empty_array_with_capacity(v___x_3304_);
v___x_3306_ = lean_array_push(v___x_3305_, v___x_3246_);
v___x_3307_ = lean_array_push(v___x_3306_, v___x_3245_);
v___x_3308_ = l_Array_append___redArg(v___x_3303_, v___x_3307_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = lean_array_push(v___x_3259_, v_heq_3252_);
v___x_3310_ = l_Array_append___redArg(v___x_3308_, v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = l_Array_append___redArg(v___x_3310_, v_alts_3256_);
lean_dec_ref(v_alts_3256_);
v___x_3312_ = l_Lean_Meta_mkLambdaFVars(v___x_3311_, v___x_3300_, v___x_3240_, v___x_3241_, v___x_3240_, v___x_3241_, v___x_3242_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec_ref(v___x_3311_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_n(v_a_3313_, 2);
lean_dec_ref(v___x_3312_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v___y_3268_);
v___x_3314_ = lean_infer_type(v_a_3313_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3350_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = lean_box(1);
lean_inc(v_declName_3260_);
v___x_3317_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3260_, v_levelParams_3261_, v_a_3315_, v_a_3313_, v___x_3316_, v___y_3271_);
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3350_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3350_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 1);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___f_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3324_ = lean_box(v___x_3240_);
lean_inc_ref(v___x_3323_);
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3325_, 0, v___x_3323_);
lean_closure_set(v___f_3325_, 1, v___x_3324_);
v___x_3326_ = lean_nat_add(v_numIndices_3262_, v___x_3263_);
lean_inc(v___x_3258_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3258_);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3263_);
v___x_3330_ = lean_array_push(v___x_3329_, v___x_3328_);
v___x_3331_ = lean_array_push(v___x_3330_, v___x_3328_);
v___x_3332_ = lean_array_push(v___x_3331_, v___x_3328_);
v___x_3333_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3333_);
lean_ctor_set(v___x_3283_, 0, v___x_3258_);
v___x_3335_ = v___x_3283_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; uint8_t v___y_3338_; uint8_t v___x_3347_; 
v___x_3336_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3336_, 0, v_numParams_3264_);
lean_ctor_set(v___x_3336_, 1, v___x_3326_);
lean_ctor_set(v___x_3336_, 2, v_snd_3265_);
lean_ctor_set(v___x_3336_, 3, v___x_3327_);
lean_ctor_set(v___x_3336_, 4, v___x_3332_);
lean_ctor_set(v___x_3336_, 5, v___x_3335_);
v___x_3347_ = l_Lean_isPrivateName(v_declName_3260_);
if (v___x_3347_ == 0)
{
v___y_3338_ = v___x_3241_;
goto v___jp_3337_;
}
else
{
v___y_3338_ = v___x_3240_;
goto v___jp_3337_;
}
v___jp_3337_:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3325_, v___y_3338_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec_ref(v___x_3339_);
v___x_3340_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3260_);
v___x_3341_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3340_, v_declName_3260_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v___x_3341_);
lean_inc_n(v_declName_3260_, 2);
v___x_3342_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3260_, v___x_3336_, v___y_3269_, v___y_3271_);
lean_dec_ref(v___x_3342_);
v___x_3343_ = 0;
v___x_3344_ = l_Lean_Meta_setInlineAttribute(v_declName_3260_, v___x_3343_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref(v___x_3344_);
v___x_3345_ = l_Lean_enableRealizationsForConst(v_declName_3260_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref(v___x_3345_);
v___x_3346_ = l_Lean_compileDecl(v___x_3323_, v___x_3241_, v___y_3270_, v___y_3271_);
return v___x_3346_;
}
else
{
lean_dec_ref(v___x_3323_);
return v___x_3345_;
}
}
else
{
lean_dec_ref(v___x_3323_);
lean_dec(v_declName_3260_);
return v___x_3344_;
}
}
else
{
lean_dec_ref(v___x_3336_);
lean_dec_ref(v___x_3323_);
lean_dec(v_declName_3260_);
return v___x_3341_;
}
}
else
{
lean_dec_ref(v___x_3336_);
lean_dec_ref(v___x_3323_);
lean_dec(v_declName_3260_);
return v___x_3339_;
}
}
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_a_3313_);
lean_del_object(v___x_3283_);
lean_dec_ref(v_snd_3265_);
lean_dec(v_numParams_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec(v___x_3258_);
v_a_3351_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3314_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3314_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_del_object(v___x_3283_);
lean_dec_ref(v_snd_3265_);
lean_dec(v_numParams_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec(v___x_3258_);
v_a_3359_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3312_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3312_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3283_);
lean_dec(v_snd_3281_);
lean_dec_ref(v_snd_3265_);
lean_dec(v_numParams_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec_ref(v___x_3259_);
lean_dec(v___x_3258_);
lean_dec_ref(v_alts_3256_);
lean_dec_ref(v_heq_3252_);
lean_dec_ref(v_params_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_is_3244_);
lean_dec_ref(v_motive_3238_);
v_a_3367_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3297_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3297_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3283_);
lean_dec(v_snd_3281_);
lean_dec_ref(v_snd_3265_);
lean_dec(v_numParams_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec_ref(v___x_3259_);
lean_dec(v___x_3258_);
lean_dec_ref(v_alts_3256_);
lean_dec(v_tail_3255_);
lean_dec(v___x_3254_);
lean_dec_ref(v_heq_3252_);
lean_dec_ref(v_params_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_is_3244_);
lean_dec_ref(v_motive_3238_);
v_a_3375_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3294_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3294_);
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
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v_snd_3265_);
lean_dec(v_numParams_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec_ref(v___x_3259_);
lean_dec(v___x_3258_);
lean_dec_ref(v_alts_3256_);
lean_dec(v_tail_3255_);
lean_dec(v___x_3254_);
lean_dec_ref(v_heq_3252_);
lean_dec_ref(v_params_3249_);
lean_dec(v___x_3248_);
lean_dec(v___x_3247_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_is_3244_);
lean_dec_ref(v_motive_3238_);
v_a_3384_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3278_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3278_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3392_ = _args[0];
lean_object* v___x_3393_ = _args[1];
lean_object* v___x_3394_ = _args[2];
lean_object* v___x_3395_ = _args[3];
lean_object* v___x_3396_ = _args[4];
lean_object* v_ism1_x27_3397_ = _args[5];
lean_object* v_is_3398_ = _args[6];
lean_object* v___x_3399_ = _args[7];
lean_object* v___x_3400_ = _args[8];
lean_object* v___x_3401_ = _args[9];
lean_object* v___x_3402_ = _args[10];
lean_object* v_params_3403_ = _args[11];
lean_object* v___x_3404_ = _args[12];
lean_object* v___x_3405_ = _args[13];
lean_object* v_heq_3406_ = _args[14];
lean_object* v_val_3407_ = _args[15];
lean_object* v___x_3408_ = _args[16];
lean_object* v_tail_3409_ = _args[17];
lean_object* v_alts_3410_ = _args[18];
lean_object* v___x_3411_ = _args[19];
lean_object* v___x_3412_ = _args[20];
lean_object* v___x_3413_ = _args[21];
lean_object* v_declName_3414_ = _args[22];
lean_object* v_levelParams_3415_ = _args[23];
lean_object* v_numIndices_3416_ = _args[24];
lean_object* v___x_3417_ = _args[25];
lean_object* v_numParams_3418_ = _args[26];
lean_object* v_snd_3419_ = _args[27];
lean_object* v_ism2_x27_3420_ = _args[28];
lean_object* v_x_3421_ = _args[29];
lean_object* v___y_3422_ = _args[30];
lean_object* v___y_3423_ = _args[31];
lean_object* v___y_3424_ = _args[32];
lean_object* v___y_3425_ = _args[33];
lean_object* v___y_3426_ = _args[34];
_start:
{
uint8_t v___x_15739__boxed_3427_; uint8_t v___x_15740__boxed_3428_; uint8_t v___x_15741__boxed_3429_; lean_object* v_res_3430_; 
v___x_15739__boxed_3427_ = lean_unbox(v___x_3394_);
v___x_15740__boxed_3428_ = lean_unbox(v___x_3395_);
v___x_15741__boxed_3429_ = lean_unbox(v___x_3396_);
v_res_3430_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3392_, v___x_3393_, v___x_15739__boxed_3427_, v___x_15740__boxed_3428_, v___x_15741__boxed_3429_, v_ism1_x27_3397_, v_is_3398_, v___x_3399_, v___x_3400_, v___x_3401_, v___x_3402_, v_params_3403_, v___x_3404_, v___x_3405_, v_heq_3406_, v_val_3407_, v___x_3408_, v_tail_3409_, v_alts_3410_, v___x_3411_, v___x_3412_, v___x_3413_, v_declName_3414_, v_levelParams_3415_, v_numIndices_3416_, v___x_3417_, v_numParams_3418_, v_snd_3419_, v_ism2_x27_3420_, v_x_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v_x_3421_);
lean_dec(v___x_3417_);
lean_dec(v_numIndices_3416_);
lean_dec_ref(v___x_3411_);
lean_dec_ref(v_val_3407_);
lean_dec_ref(v___x_3405_);
lean_dec_ref(v___x_3404_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3431_, lean_object* v___x_3432_, uint8_t v___x_3433_, uint8_t v___x_3434_, uint8_t v___x_3435_, lean_object* v_is_3436_, lean_object* v___x_3437_, lean_object* v___x_3438_, lean_object* v___x_3439_, lean_object* v___x_3440_, lean_object* v_params_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v_heq_3444_, lean_object* v_val_3445_, lean_object* v___x_3446_, lean_object* v_tail_3447_, lean_object* v_alts_3448_, lean_object* v___x_3449_, lean_object* v___x_3450_, lean_object* v___x_3451_, lean_object* v_declName_3452_, lean_object* v_levelParams_3453_, lean_object* v_numIndices_3454_, lean_object* v___x_3455_, lean_object* v_numParams_3456_, lean_object* v_snd_3457_, lean_object* v___x_3458_, lean_object* v___x_3459_, lean_object* v_ism1_x27_3460_, lean_object* v_x_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___f_3470_; lean_object* v___x_3471_; 
v___x_3467_ = lean_box(v___x_3433_);
v___x_3468_ = lean_box(v___x_3434_);
v___x_3469_ = lean_box(v___x_3435_);
v___f_3470_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 35, 28);
lean_closure_set(v___f_3470_, 0, v_motive_3431_);
lean_closure_set(v___f_3470_, 1, v___x_3432_);
lean_closure_set(v___f_3470_, 2, v___x_3467_);
lean_closure_set(v___f_3470_, 3, v___x_3468_);
lean_closure_set(v___f_3470_, 4, v___x_3469_);
lean_closure_set(v___f_3470_, 5, v_ism1_x27_3460_);
lean_closure_set(v___f_3470_, 6, v_is_3436_);
lean_closure_set(v___f_3470_, 7, v___x_3437_);
lean_closure_set(v___f_3470_, 8, v___x_3438_);
lean_closure_set(v___f_3470_, 9, v___x_3439_);
lean_closure_set(v___f_3470_, 10, v___x_3440_);
lean_closure_set(v___f_3470_, 11, v_params_3441_);
lean_closure_set(v___f_3470_, 12, v___x_3442_);
lean_closure_set(v___f_3470_, 13, v___x_3443_);
lean_closure_set(v___f_3470_, 14, v_heq_3444_);
lean_closure_set(v___f_3470_, 15, v_val_3445_);
lean_closure_set(v___f_3470_, 16, v___x_3446_);
lean_closure_set(v___f_3470_, 17, v_tail_3447_);
lean_closure_set(v___f_3470_, 18, v_alts_3448_);
lean_closure_set(v___f_3470_, 19, v___x_3449_);
lean_closure_set(v___f_3470_, 20, v___x_3450_);
lean_closure_set(v___f_3470_, 21, v___x_3451_);
lean_closure_set(v___f_3470_, 22, v_declName_3452_);
lean_closure_set(v___f_3470_, 23, v_levelParams_3453_);
lean_closure_set(v___f_3470_, 24, v_numIndices_3454_);
lean_closure_set(v___f_3470_, 25, v___x_3455_);
lean_closure_set(v___f_3470_, 26, v_numParams_3456_);
lean_closure_set(v___f_3470_, 27, v_snd_3457_);
v___x_3471_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3458_, v___x_3459_, v___f_3470_, v___x_3433_, v___x_3433_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3472_ = _args[0];
lean_object* v___x_3473_ = _args[1];
lean_object* v___x_3474_ = _args[2];
lean_object* v___x_3475_ = _args[3];
lean_object* v___x_3476_ = _args[4];
lean_object* v_is_3477_ = _args[5];
lean_object* v___x_3478_ = _args[6];
lean_object* v___x_3479_ = _args[7];
lean_object* v___x_3480_ = _args[8];
lean_object* v___x_3481_ = _args[9];
lean_object* v_params_3482_ = _args[10];
lean_object* v___x_3483_ = _args[11];
lean_object* v___x_3484_ = _args[12];
lean_object* v_heq_3485_ = _args[13];
lean_object* v_val_3486_ = _args[14];
lean_object* v___x_3487_ = _args[15];
lean_object* v_tail_3488_ = _args[16];
lean_object* v_alts_3489_ = _args[17];
lean_object* v___x_3490_ = _args[18];
lean_object* v___x_3491_ = _args[19];
lean_object* v___x_3492_ = _args[20];
lean_object* v_declName_3493_ = _args[21];
lean_object* v_levelParams_3494_ = _args[22];
lean_object* v_numIndices_3495_ = _args[23];
lean_object* v___x_3496_ = _args[24];
lean_object* v_numParams_3497_ = _args[25];
lean_object* v_snd_3498_ = _args[26];
lean_object* v___x_3499_ = _args[27];
lean_object* v___x_3500_ = _args[28];
lean_object* v_ism1_x27_3501_ = _args[29];
lean_object* v_x_3502_ = _args[30];
lean_object* v___y_3503_ = _args[31];
lean_object* v___y_3504_ = _args[32];
lean_object* v___y_3505_ = _args[33];
lean_object* v___y_3506_ = _args[34];
lean_object* v___y_3507_ = _args[35];
_start:
{
uint8_t v___x_16063__boxed_3508_; uint8_t v___x_16064__boxed_3509_; uint8_t v___x_16065__boxed_3510_; lean_object* v_res_3511_; 
v___x_16063__boxed_3508_ = lean_unbox(v___x_3474_);
v___x_16064__boxed_3509_ = lean_unbox(v___x_3475_);
v___x_16065__boxed_3510_ = lean_unbox(v___x_3476_);
v_res_3511_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3472_, v___x_3473_, v___x_16063__boxed_3508_, v___x_16064__boxed_3509_, v___x_16065__boxed_3510_, v_is_3477_, v___x_3478_, v___x_3479_, v___x_3480_, v___x_3481_, v_params_3482_, v___x_3483_, v___x_3484_, v_heq_3485_, v_val_3486_, v___x_3487_, v_tail_3488_, v_alts_3489_, v___x_3490_, v___x_3491_, v___x_3492_, v_declName_3493_, v_levelParams_3494_, v_numIndices_3495_, v___x_3496_, v_numParams_3497_, v_snd_3498_, v___x_3499_, v___x_3500_, v_ism1_x27_3501_, v_x_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_x_3502_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3512_, lean_object* v___x_3513_, lean_object* v_motive_3514_, lean_object* v___x_3515_, uint8_t v___x_3516_, uint8_t v___x_3517_, uint8_t v___x_3518_, lean_object* v_is_3519_, lean_object* v___x_3520_, lean_object* v___x_3521_, lean_object* v___x_3522_, lean_object* v___x_3523_, lean_object* v_params_3524_, lean_object* v___x_3525_, lean_object* v___x_3526_, lean_object* v_heq_3527_, lean_object* v_val_3528_, lean_object* v___x_3529_, lean_object* v_tail_3530_, lean_object* v___x_3531_, lean_object* v___x_3532_, lean_object* v___x_3533_, lean_object* v_declName_3534_, lean_object* v_levelParams_3535_, lean_object* v___x_3536_, lean_object* v_numParams_3537_, lean_object* v_snd_3538_, lean_object* v___x_3539_, lean_object* v_alts_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___f_3551_; lean_object* v___x_3552_; 
v___x_3546_ = lean_nat_add(v_numIndices_3512_, v___x_3513_);
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
v___x_3548_ = lean_box(v___x_3516_);
v___x_3549_ = lean_box(v___x_3517_);
v___x_3550_ = lean_box(v___x_3518_);
lean_inc_ref(v___x_3547_);
lean_inc_ref(v___x_3539_);
v___f_3551_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 36, 29);
lean_closure_set(v___f_3551_, 0, v_motive_3514_);
lean_closure_set(v___f_3551_, 1, v___x_3515_);
lean_closure_set(v___f_3551_, 2, v___x_3548_);
lean_closure_set(v___f_3551_, 3, v___x_3549_);
lean_closure_set(v___f_3551_, 4, v___x_3550_);
lean_closure_set(v___f_3551_, 5, v_is_3519_);
lean_closure_set(v___f_3551_, 6, v___x_3520_);
lean_closure_set(v___f_3551_, 7, v___x_3521_);
lean_closure_set(v___f_3551_, 8, v___x_3522_);
lean_closure_set(v___f_3551_, 9, v___x_3523_);
lean_closure_set(v___f_3551_, 10, v_params_3524_);
lean_closure_set(v___f_3551_, 11, v___x_3525_);
lean_closure_set(v___f_3551_, 12, v___x_3526_);
lean_closure_set(v___f_3551_, 13, v_heq_3527_);
lean_closure_set(v___f_3551_, 14, v_val_3528_);
lean_closure_set(v___f_3551_, 15, v___x_3529_);
lean_closure_set(v___f_3551_, 16, v_tail_3530_);
lean_closure_set(v___f_3551_, 17, v_alts_3540_);
lean_closure_set(v___f_3551_, 18, v___x_3531_);
lean_closure_set(v___f_3551_, 19, v___x_3532_);
lean_closure_set(v___f_3551_, 20, v___x_3533_);
lean_closure_set(v___f_3551_, 21, v_declName_3534_);
lean_closure_set(v___f_3551_, 22, v_levelParams_3535_);
lean_closure_set(v___f_3551_, 23, v_numIndices_3512_);
lean_closure_set(v___f_3551_, 24, v___x_3536_);
lean_closure_set(v___f_3551_, 25, v_numParams_3537_);
lean_closure_set(v___f_3551_, 26, v_snd_3538_);
lean_closure_set(v___f_3551_, 27, v___x_3539_);
lean_closure_set(v___f_3551_, 28, v___x_3547_);
v___x_3552_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3539_, v___x_3547_, v___f_3551_, v___x_3516_, v___x_3516_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3553_ = _args[0];
lean_object* v___x_3554_ = _args[1];
lean_object* v_motive_3555_ = _args[2];
lean_object* v___x_3556_ = _args[3];
lean_object* v___x_3557_ = _args[4];
lean_object* v___x_3558_ = _args[5];
lean_object* v___x_3559_ = _args[6];
lean_object* v_is_3560_ = _args[7];
lean_object* v___x_3561_ = _args[8];
lean_object* v___x_3562_ = _args[9];
lean_object* v___x_3563_ = _args[10];
lean_object* v___x_3564_ = _args[11];
lean_object* v_params_3565_ = _args[12];
lean_object* v___x_3566_ = _args[13];
lean_object* v___x_3567_ = _args[14];
lean_object* v_heq_3568_ = _args[15];
lean_object* v_val_3569_ = _args[16];
lean_object* v___x_3570_ = _args[17];
lean_object* v_tail_3571_ = _args[18];
lean_object* v___x_3572_ = _args[19];
lean_object* v___x_3573_ = _args[20];
lean_object* v___x_3574_ = _args[21];
lean_object* v_declName_3575_ = _args[22];
lean_object* v_levelParams_3576_ = _args[23];
lean_object* v___x_3577_ = _args[24];
lean_object* v_numParams_3578_ = _args[25];
lean_object* v_snd_3579_ = _args[26];
lean_object* v___x_3580_ = _args[27];
lean_object* v_alts_3581_ = _args[28];
lean_object* v___y_3582_ = _args[29];
lean_object* v___y_3583_ = _args[30];
lean_object* v___y_3584_ = _args[31];
lean_object* v___y_3585_ = _args[32];
lean_object* v___y_3586_ = _args[33];
_start:
{
uint8_t v___x_16152__boxed_3587_; uint8_t v___x_16153__boxed_3588_; uint8_t v___x_16154__boxed_3589_; lean_object* v_res_3590_; 
v___x_16152__boxed_3587_ = lean_unbox(v___x_3557_);
v___x_16153__boxed_3588_ = lean_unbox(v___x_3558_);
v___x_16154__boxed_3589_ = lean_unbox(v___x_3559_);
v_res_3590_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3553_, v___x_3554_, v_motive_3555_, v___x_3556_, v___x_16152__boxed_3587_, v___x_16153__boxed_3588_, v___x_16154__boxed_3589_, v_is_3560_, v___x_3561_, v___x_3562_, v___x_3563_, v___x_3564_, v_params_3565_, v___x_3566_, v___x_3567_, v_heq_3568_, v_val_3569_, v___x_3570_, v_tail_3571_, v___x_3572_, v___x_3573_, v___x_3574_, v_declName_3575_, v_levelParams_3576_, v___x_3577_, v_numParams_3578_, v_snd_3579_, v___x_3580_, v_alts_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___x_3554_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3591_, lean_object* v_declInfos_3592_, lean_object* v_k_3593_, lean_object* v_kind_3594_, lean_object* v_x_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
uint8_t v_kind_boxed_3601_; lean_object* v_res_3602_; 
v_kind_boxed_3601_ = lean_unbox(v_kind_3594_);
v_res_3602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3591_, v_declInfos_3592_, v_k_3593_, v_kind_boxed_3601_, v_x_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3603_, lean_object* v_k_3604_, uint8_t v_kind_3605_, lean_object* v_acc_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; lean_object* v_toApplicative_3613_; lean_object* v_toFunctor_3614_; lean_object* v_toSeq_3615_; lean_object* v_toSeqLeft_3616_; lean_object* v_toSeqRight_3617_; lean_object* v___f_3618_; lean_object* v___f_3619_; lean_object* v___f_3620_; lean_object* v___f_3621_; lean_object* v___x_3622_; lean_object* v___f_3623_; lean_object* v___f_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v_toApplicative_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3686_; 
v___x_3612_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3613_ = lean_ctor_get(v___x_3612_, 0);
v_toFunctor_3614_ = lean_ctor_get(v_toApplicative_3613_, 0);
v_toSeq_3615_ = lean_ctor_get(v_toApplicative_3613_, 2);
v_toSeqLeft_3616_ = lean_ctor_get(v_toApplicative_3613_, 3);
v_toSeqRight_3617_ = lean_ctor_get(v_toApplicative_3613_, 4);
v___f_3618_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3619_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3614_, 2);
v___f_3620_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3620_, 0, v_toFunctor_3614_);
v___f_3621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3621_, 0, v_toFunctor_3614_);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___f_3620_);
lean_ctor_set(v___x_3622_, 1, v___f_3621_);
lean_inc(v_toSeqRight_3617_);
v___f_3623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3623_, 0, v_toSeqRight_3617_);
lean_inc(v_toSeqLeft_3616_);
v___f_3624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3624_, 0, v_toSeqLeft_3616_);
lean_inc(v_toSeq_3615_);
v___f_3625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3625_, 0, v_toSeq_3615_);
v___x_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3622_);
lean_ctor_set(v___x_3626_, 1, v___f_3618_);
lean_ctor_set(v___x_3626_, 2, v___f_3625_);
lean_ctor_set(v___x_3626_, 3, v___f_3624_);
lean_ctor_set(v___x_3626_, 4, v___f_3623_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
lean_ctor_set(v___x_3627_, 1, v___f_3619_);
v___x_3628_ = l_StateRefT_x27_instMonad___redArg(v___x_3627_);
v_toApplicative_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v___x_3628_, 1);
lean_dec(v_unused_3687_);
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3686_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_toApplicative_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3686_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v_toFunctor_3633_; lean_object* v_toSeq_3634_; lean_object* v_toSeqLeft_3635_; lean_object* v_toSeqRight_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3684_; 
v_toFunctor_3633_ = lean_ctor_get(v_toApplicative_3629_, 0);
v_toSeq_3634_ = lean_ctor_get(v_toApplicative_3629_, 2);
v_toSeqLeft_3635_ = lean_ctor_get(v_toApplicative_3629_, 3);
v_toSeqRight_3636_ = lean_ctor_get(v_toApplicative_3629_, 4);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_toApplicative_3629_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; 
v_unused_3685_ = lean_ctor_get(v_toApplicative_3629_, 1);
lean_dec(v_unused_3685_);
v___x_3638_ = v_toApplicative_3629_;
v_isShared_3639_ = v_isSharedCheck_3684_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_toSeqRight_3636_);
lean_inc(v_toSeqLeft_3635_);
lean_inc(v_toSeq_3634_);
lean_inc(v_toFunctor_3633_);
lean_dec(v_toApplicative_3629_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3684_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___f_3640_; lean_object* v___f_3641_; lean_object* v___f_3642_; lean_object* v___f_3643_; lean_object* v___x_3644_; lean_object* v___f_3645_; lean_object* v___f_3646_; lean_object* v___f_3647_; lean_object* v___x_3649_; 
v___f_3640_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3641_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3633_);
v___f_3642_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3642_, 0, v_toFunctor_3633_);
v___f_3643_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3643_, 0, v_toFunctor_3633_);
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___f_3642_);
lean_ctor_set(v___x_3644_, 1, v___f_3643_);
v___f_3645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3645_, 0, v_toSeqRight_3636_);
v___f_3646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3646_, 0, v_toSeqLeft_3635_);
v___f_3647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3647_, 0, v_toSeq_3634_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 4, v___f_3645_);
lean_ctor_set(v___x_3638_, 3, v___f_3646_);
lean_ctor_set(v___x_3638_, 2, v___f_3647_);
lean_ctor_set(v___x_3638_, 1, v___f_3640_);
lean_ctor_set(v___x_3638_, 0, v___x_3644_);
v___x_3649_ = v___x_3638_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___f_3640_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v___f_3647_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v___f_3646_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v___f_3645_);
v___x_3649_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3651_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___f_3641_);
lean_ctor_set(v___x_3631_, 0, v___x_3649_);
v___x_3651_ = v___x_3631_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___f_3641_);
v___x_3651_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = lean_array_get_size(v_acc_3606_);
v___x_3653_ = lean_array_get_size(v_declInfos_3603_);
v___x_3654_ = lean_nat_dec_lt(v___x_3652_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_declInfos_3603_);
lean_inc(v___y_3610_);
lean_inc_ref(v___y_3609_);
lean_inc(v___y_3608_);
lean_inc_ref(v___y_3607_);
v___x_3655_ = lean_apply_6(v_k_3604_, v_acc_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, lean_box(0));
return v___x_3655_;
}
else
{
lean_object* v___f_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v_snd_3664_; lean_object* v_fst_3665_; lean_object* v_fst_3666_; lean_object* v_snd_3667_; lean_object* v___x_3668_; 
v___f_3656_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3656_, 0, v___x_3651_);
v___x_3657_ = lean_box(0);
v___x_3658_ = 0;
v___f_3659_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3659_, 0, v___f_3656_);
v___x_3660_ = lean_box(v___x_3658_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___f_3659_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3657_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_array_get(v___x_3662_, v_declInfos_3603_, v___x_3652_);
lean_dec_ref(v___x_3662_);
v_snd_3664_ = lean_ctor_get(v___x_3663_, 1);
lean_inc(v_snd_3664_);
v_fst_3665_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_fst_3665_);
lean_dec(v___x_3663_);
v_fst_3666_ = lean_ctor_get(v_snd_3664_, 0);
lean_inc(v_fst_3666_);
v_snd_3667_ = lean_ctor_get(v_snd_3664_, 1);
lean_inc(v_snd_3667_);
lean_dec(v_snd_3664_);
lean_inc(v___y_3610_);
lean_inc_ref(v___y_3609_);
lean_inc(v___y_3608_);
lean_inc_ref(v___y_3607_);
lean_inc_ref(v_acc_3606_);
v___x_3668_ = lean_apply_6(v_snd_3667_, v_acc_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, lean_box(0));
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; lean_object* v___f_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref(v___x_3668_);
v___x_3670_ = lean_box(v_kind_3605_);
v___f_3671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3671_, 0, v_acc_3606_);
lean_closure_set(v___f_3671_, 1, v_declInfos_3603_);
lean_closure_set(v___f_3671_, 2, v_k_3604_);
lean_closure_set(v___f_3671_, 3, v___x_3670_);
v___x_3672_ = lean_unbox(v_fst_3666_);
lean_dec(v_fst_3666_);
v___x_3673_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3665_, v___x_3672_, v_a_3669_, v___f_3671_, v_kind_3605_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3673_;
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_fst_3666_);
lean_dec(v_fst_3665_);
lean_dec_ref(v_acc_3606_);
lean_dec_ref(v_k_3604_);
lean_dec_ref(v_declInfos_3603_);
v_a_3674_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3668_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3668_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3688_, lean_object* v_declInfos_3689_, lean_object* v_k_3690_, uint8_t v_kind_3691_, lean_object* v_x_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_array_push(v_acc_3688_, v_x_3692_);
v___x_3699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3689_, v_k_3690_, v_kind_3691_, v___x_3698_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3700_, lean_object* v_k_3701_, lean_object* v_kind_3702_, lean_object* v_acc_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v_kind_boxed_3709_; lean_object* v_res_3710_; 
v_kind_boxed_3709_ = lean_unbox(v_kind_3702_);
v_res_3710_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3700_, v_k_3701_, v_kind_boxed_3709_, v_acc_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3711_, lean_object* v_k_3712_, uint8_t v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3711_, v_k_3712_, v_kind_3713_, v___x_3719_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3721_, lean_object* v_k_3722_, lean_object* v_kind_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v_kind_boxed_3729_; lean_object* v_res_3730_; 
v_kind_boxed_3729_ = lean_unbox(v_kind_3723_);
v_res_3730_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3721_, v_k_3722_, v_kind_boxed_3729_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3731_, lean_object* v_k_3732_, uint8_t v_kind_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
size_t v_sz_3739_; size_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_sz_3739_ = lean_array_size(v_declInfos_3731_);
v___x_3740_ = ((size_t)0ULL);
v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3739_, v___x_3740_, v_declInfos_3731_);
v___x_3742_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3741_, v_k_3732_, v_kind_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3743_, lean_object* v_k_3744_, lean_object* v_kind_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
uint8_t v_kind_boxed_3751_; lean_object* v_res_3752_; 
v_kind_boxed_3751_ = lean_unbox(v_kind_3745_);
v_res_3752_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3743_, v_k_3744_, v_kind_boxed_3751_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3753_, lean_object* v_k_3754_, uint8_t v_kind_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
size_t v_sz_3761_; size_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_sz_3761_ = lean_array_size(v_declInfos_3753_);
v___x_3762_ = ((size_t)0ULL);
v___x_3763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3761_, v___x_3762_, v_declInfos_3753_);
v___x_3764_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3763_, v_k_3754_, v_kind_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3765_, lean_object* v_k_3766_, lean_object* v_kind_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
uint8_t v_kind_boxed_3773_; lean_object* v_res_3774_; 
v_kind_boxed_3773_ = lean_unbox(v_kind_3767_);
v_res_3774_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3765_, v_k_3766_, v_kind_boxed_3773_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
return v_res_3774_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3777_ = lean_box(0);
v___x_3778_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3779_ = l_Lean_mkConst(v___x_3778_, v___x_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v_j_3780_, lean_object* v___x_3781_, lean_object* v_motive_3782_, uint8_t v_isZero_3783_, uint8_t v___x_3784_, uint8_t v___x_3785_, lean_object* v___x_3786_, lean_object* v___x_3787_, lean_object* v___x_3788_, lean_object* v_zs12_3789_, lean_object* v_is_3790_, lean_object* v_fields1_3791_, lean_object* v_fields2_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v_e_3808_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_inc(v_j_3780_);
v___x_3818_ = l_Lean_mkNatLit(v_j_3780_);
v___x_3819_ = l_Lean_Meta_mkEqRefl(v___x_3818_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
lean_inc_ref(v___x_3781_);
v___x_3821_ = l_Lean_mkAppN(v___x_3781_, v_fields1_3791_);
v___x_3822_ = l_Lean_mkAppN(v___x_3781_, v_fields2_3792_);
v___x_3823_ = lean_unsigned_to_nat(3u);
v___x_3824_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___x_3825_ = lean_array_push(v___x_3824_, v___x_3821_);
v___x_3826_ = lean_array_push(v___x_3825_, v___x_3822_);
v___x_3827_ = lean_array_push(v___x_3826_, v_a_3820_);
v___x_3828_ = l_Array_append___redArg(v_is_3790_, v___x_3827_);
lean_dec_ref(v___x_3827_);
v___x_3829_ = l_Lean_mkAppN(v_motive_3782_, v___x_3828_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = l_Lean_Meta_mkForallFVars(v_zs12_3789_, v___x_3829_, v_isZero_3783_, v___x_3784_, v___x_3784_, v___x_3785_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
v___x_3832_ = lean_array_get_size(v_zs12_3789_);
v___x_3833_ = lean_nat_dec_eq(v___x_3832_, v___x_3786_);
if (v___x_3833_ == 0)
{
v_e_3808_ = v_a_3831_;
goto v___jp_3807_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3835_ = l_Lean_mkArrow(v___x_3834_, v_a_3831_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3835_);
v_e_3808_ = v_a_3836_;
goto v___jp_3807_;
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v___x_3787_);
lean_dec(v___x_3786_);
lean_dec(v_j_3780_);
v_a_3837_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3835_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3835_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v___x_3787_);
lean_dec(v___x_3786_);
lean_dec(v_j_3780_);
v_a_3845_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3830_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3830_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec_ref(v_is_3790_);
lean_dec(v___x_3787_);
lean_dec(v___x_3786_);
lean_dec_ref(v_motive_3782_);
lean_dec_ref(v___x_3781_);
lean_dec(v_j_3780_);
v_a_3853_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3819_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3819_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
v___jp_3798_:
{
lean_object* v___x_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3801_ = lean_array_get_size(v_zs12_3789_);
v___x_3802_ = lean_nat_dec_eq(v___x_3801_, v___x_3786_);
v___x_3803_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3786_);
lean_ctor_set_uint8(v___x_3803_, sizeof(void*)*2, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___y_3800_);
lean_ctor_set(v___x_3804_, 1, v___y_3799_);
v___x_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
lean_ctor_set(v___x_3805_, 1, v___x_3803_);
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
v___jp_3807_:
{
if (lean_obj_tag(v___x_3787_) == 1)
{
lean_object* v_str_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
lean_dec(v_j_3780_);
v_str_3809_ = lean_ctor_get(v___x_3787_, 1);
lean_inc_ref(v_str_3809_);
lean_dec_ref(v___x_3787_);
v___x_3810_ = lean_box(0);
v___x_3811_ = l_Lean_Name_str___override(v___x_3810_, v_str_3809_);
v___y_3799_ = v_e_3808_;
v___y_3800_ = v___x_3811_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_dec(v___x_3787_);
v___x_3812_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3813_ = lean_nat_add(v_j_3780_, v___x_3788_);
lean_dec(v_j_3780_);
v___x_3814_ = l_Nat_reprFast(v___x_3813_);
v___x_3815_ = lean_string_append(v___x_3812_, v___x_3814_);
lean_dec_ref(v___x_3814_);
v___x_3816_ = lean_box(0);
v___x_3817_ = l_Lean_Name_str___override(v___x_3816_, v___x_3815_);
v___y_3799_ = v_e_3808_;
v___y_3800_ = v___x_3817_;
goto v___jp_3798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_j_3861_ = _args[0];
lean_object* v___x_3862_ = _args[1];
lean_object* v_motive_3863_ = _args[2];
lean_object* v_isZero_3864_ = _args[3];
lean_object* v___x_3865_ = _args[4];
lean_object* v___x_3866_ = _args[5];
lean_object* v___x_3867_ = _args[6];
lean_object* v___x_3868_ = _args[7];
lean_object* v___x_3869_ = _args[8];
lean_object* v_zs12_3870_ = _args[9];
lean_object* v_is_3871_ = _args[10];
lean_object* v_fields1_3872_ = _args[11];
lean_object* v_fields2_3873_ = _args[12];
lean_object* v___y_3874_ = _args[13];
lean_object* v___y_3875_ = _args[14];
lean_object* v___y_3876_ = _args[15];
lean_object* v___y_3877_ = _args[16];
lean_object* v___y_3878_ = _args[17];
_start:
{
uint8_t v_isZero_boxed_3879_; uint8_t v___x_16490__boxed_3880_; uint8_t v___x_16491__boxed_3881_; lean_object* v_res_3882_; 
v_isZero_boxed_3879_ = lean_unbox(v_isZero_3864_);
v___x_16490__boxed_3880_ = lean_unbox(v___x_3865_);
v___x_16491__boxed_3881_ = lean_unbox(v___x_3866_);
v_res_3882_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v_j_3861_, v___x_3862_, v_motive_3863_, v_isZero_boxed_3879_, v___x_16490__boxed_3880_, v___x_16491__boxed_3881_, v___x_3867_, v___x_3868_, v___x_3869_, v_zs12_3870_, v_is_3871_, v_fields1_3872_, v_fields2_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v_fields2_3873_);
lean_dec_ref(v_fields1_3872_);
lean_dec_ref(v_zs12_3870_);
lean_dec(v___x_3869_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3883_, lean_object* v_params_3884_, lean_object* v_motive_3885_, lean_object* v_as_3886_, lean_object* v_i_3887_, lean_object* v_j_3888_, lean_object* v_bs_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_zero_3895_; uint8_t v_isZero_3896_; 
v_zero_3895_ = lean_unsigned_to_nat(0u);
v_isZero_3896_ = lean_nat_dec_eq(v_i_3887_, v_zero_3895_);
if (v_isZero_3896_ == 1)
{
lean_object* v___x_3897_; 
lean_dec(v_j_3888_);
lean_dec(v_i_3887_);
lean_dec_ref(v_motive_3885_);
lean_dec(v_tail_3883_);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v_bs_3889_);
return v___x_3897_;
}
else
{
lean_object* v___x_3898_; uint8_t v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; 
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = 1;
v___x_3900_ = 1;
v___x_3901_ = lean_array_fget_borrowed(v_as_3886_, v_j_3888_);
lean_inc(v_tail_3883_);
lean_inc_n(v___x_3901_, 2);
v___x_3902_ = l_Lean_mkConst(v___x_3901_, v_tail_3883_);
v___x_3903_ = l_Lean_mkAppN(v___x_3902_, v_params_3884_);
v___x_3904_ = lean_box(v_isZero_3896_);
v___x_3905_ = lean_box(v___x_3899_);
v___x_3906_ = lean_box(v___x_3900_);
lean_inc_ref(v_motive_3885_);
lean_inc_ref(v___x_3903_);
lean_inc(v_j_3888_);
v___f_3907_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3907_, 0, v_j_3888_);
lean_closure_set(v___f_3907_, 1, v___x_3903_);
lean_closure_set(v___f_3907_, 2, v_motive_3885_);
lean_closure_set(v___f_3907_, 3, v___x_3904_);
lean_closure_set(v___f_3907_, 4, v___x_3905_);
lean_closure_set(v___f_3907_, 5, v___x_3906_);
lean_closure_set(v___f_3907_, 6, v_zero_3895_);
lean_closure_set(v___f_3907_, 7, v___x_3901_);
lean_closure_set(v___f_3907_, 8, v___x_3898_);
v___x_3908_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3903_, v___f_3907_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v_n_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3908_);
v_n_3910_ = lean_nat_sub(v_i_3887_, v___x_3898_);
lean_dec(v_i_3887_);
v___x_3911_ = lean_nat_add(v_j_3888_, v___x_3898_);
lean_dec(v_j_3888_);
v___x_3912_ = lean_array_push(v_bs_3889_, v_a_3909_);
v_i_3887_ = v_n_3910_;
v_j_3888_ = v___x_3911_;
v_bs_3889_ = v___x_3912_;
goto _start;
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref(v_bs_3889_);
lean_dec(v_j_3888_);
lean_dec(v_i_3887_);
lean_dec_ref(v_motive_3885_);
lean_dec(v_tail_3883_);
v_a_3914_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3908_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3908_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3922_, lean_object* v_params_3923_, lean_object* v_motive_3924_, lean_object* v_as_3925_, lean_object* v_i_3926_, lean_object* v_j_3927_, lean_object* v_bs_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3922_, v_params_3923_, v_motive_3924_, v_as_3925_, v_i_3926_, v_j_3927_, v_bs_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec_ref(v_as_3925_);
lean_dec_ref(v_params_3923_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3935_, lean_object* v_tail_3936_, lean_object* v_params_3937_, lean_object* v___x_3938_, lean_object* v_numIndices_3939_, lean_object* v___x_3940_, lean_object* v___x_3941_, uint8_t v___x_3942_, uint8_t v___x_3943_, uint8_t v___x_3944_, lean_object* v_is_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v___x_3948_, lean_object* v___x_3949_, lean_object* v___x_3950_, lean_object* v___x_3951_, lean_object* v_heq_3952_, lean_object* v_val_3953_, lean_object* v___x_3954_, lean_object* v_declName_3955_, lean_object* v_levelParams_3956_, lean_object* v___x_3957_, lean_object* v_numParams_3958_, lean_object* v___x_3959_, lean_object* v_motive_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3966_ = lean_array_mk(v_ctors_3935_);
v___x_3967_ = lean_array_get_size(v___x_3966_);
v___x_3968_ = lean_mk_empty_array_with_capacity(v___x_3967_);
lean_inc(v___x_3938_);
lean_inc_ref(v_motive_3960_);
lean_inc(v_tail_3936_);
v___x_3969_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3936_, v_params_3937_, v_motive_3960_, v___x_3966_, v___x_3967_, v___x_3938_, v___x_3968_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; lean_object* v_fst_3972_; lean_object* v_snd_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___f_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v___x_3971_ = l_Array_unzip___redArg(v_a_3970_);
lean_dec(v_a_3970_);
v_fst_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_fst_3972_);
v_snd_3973_ = lean_ctor_get(v___x_3971_, 1);
lean_inc(v_snd_3973_);
lean_dec_ref(v___x_3971_);
v___x_3974_ = lean_box(v___x_3942_);
v___x_3975_ = lean_box(v___x_3943_);
v___x_3976_ = lean_box(v___x_3944_);
v___f_3977_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 34, 28);
lean_closure_set(v___f_3977_, 0, v_numIndices_3939_);
lean_closure_set(v___f_3977_, 1, v___x_3940_);
lean_closure_set(v___f_3977_, 2, v_motive_3960_);
lean_closure_set(v___f_3977_, 3, v___x_3941_);
lean_closure_set(v___f_3977_, 4, v___x_3974_);
lean_closure_set(v___f_3977_, 5, v___x_3975_);
lean_closure_set(v___f_3977_, 6, v___x_3976_);
lean_closure_set(v___f_3977_, 7, v_is_3945_);
lean_closure_set(v___f_3977_, 8, v___x_3946_);
lean_closure_set(v___f_3977_, 9, v___x_3947_);
lean_closure_set(v___f_3977_, 10, v___x_3948_);
lean_closure_set(v___f_3977_, 11, v___x_3949_);
lean_closure_set(v___f_3977_, 12, v_params_3937_);
lean_closure_set(v___f_3977_, 13, v___x_3950_);
lean_closure_set(v___f_3977_, 14, v___x_3951_);
lean_closure_set(v___f_3977_, 15, v_heq_3952_);
lean_closure_set(v___f_3977_, 16, v_val_3953_);
lean_closure_set(v___f_3977_, 17, v___x_3967_);
lean_closure_set(v___f_3977_, 18, v_tail_3936_);
lean_closure_set(v___f_3977_, 19, v___x_3966_);
lean_closure_set(v___f_3977_, 20, v___x_3938_);
lean_closure_set(v___f_3977_, 21, v___x_3954_);
lean_closure_set(v___f_3977_, 22, v_declName_3955_);
lean_closure_set(v___f_3977_, 23, v_levelParams_3956_);
lean_closure_set(v___f_3977_, 24, v___x_3957_);
lean_closure_set(v___f_3977_, 25, v_numParams_3958_);
lean_closure_set(v___f_3977_, 26, v_snd_3973_);
lean_closure_set(v___f_3977_, 27, v___x_3959_);
v___x_3978_ = 0;
v___x_3979_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3972_, v___f_3977_, v___x_3978_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3979_;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v___x_3966_);
lean_dec_ref(v_motive_3960_);
lean_dec_ref(v___x_3959_);
lean_dec(v_numParams_3958_);
lean_dec(v___x_3957_);
lean_dec(v_levelParams_3956_);
lean_dec(v_declName_3955_);
lean_dec_ref(v___x_3954_);
lean_dec_ref(v_val_3953_);
lean_dec_ref(v_heq_3952_);
lean_dec_ref(v___x_3951_);
lean_dec_ref(v___x_3950_);
lean_dec(v___x_3949_);
lean_dec(v___x_3948_);
lean_dec_ref(v___x_3947_);
lean_dec_ref(v___x_3946_);
lean_dec_ref(v_is_3945_);
lean_dec_ref(v___x_3941_);
lean_dec(v___x_3940_);
lean_dec(v_numIndices_3939_);
lean_dec(v___x_3938_);
lean_dec_ref(v_params_3937_);
lean_dec(v_tail_3936_);
v_a_3980_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3969_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3969_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_3988_ = _args[0];
lean_object* v_tail_3989_ = _args[1];
lean_object* v_params_3990_ = _args[2];
lean_object* v___x_3991_ = _args[3];
lean_object* v_numIndices_3992_ = _args[4];
lean_object* v___x_3993_ = _args[5];
lean_object* v___x_3994_ = _args[6];
lean_object* v___x_3995_ = _args[7];
lean_object* v___x_3996_ = _args[8];
lean_object* v___x_3997_ = _args[9];
lean_object* v_is_3998_ = _args[10];
lean_object* v___x_3999_ = _args[11];
lean_object* v___x_4000_ = _args[12];
lean_object* v___x_4001_ = _args[13];
lean_object* v___x_4002_ = _args[14];
lean_object* v___x_4003_ = _args[15];
lean_object* v___x_4004_ = _args[16];
lean_object* v_heq_4005_ = _args[17];
lean_object* v_val_4006_ = _args[18];
lean_object* v___x_4007_ = _args[19];
lean_object* v_declName_4008_ = _args[20];
lean_object* v_levelParams_4009_ = _args[21];
lean_object* v___x_4010_ = _args[22];
lean_object* v_numParams_4011_ = _args[23];
lean_object* v___x_4012_ = _args[24];
lean_object* v_motive_4013_ = _args[25];
lean_object* v___y_4014_ = _args[26];
lean_object* v___y_4015_ = _args[27];
lean_object* v___y_4016_ = _args[28];
lean_object* v___y_4017_ = _args[29];
lean_object* v___y_4018_ = _args[30];
_start:
{
uint8_t v___x_16724__boxed_4019_; uint8_t v___x_16725__boxed_4020_; uint8_t v___x_16726__boxed_4021_; lean_object* v_res_4022_; 
v___x_16724__boxed_4019_ = lean_unbox(v___x_3995_);
v___x_16725__boxed_4020_ = lean_unbox(v___x_3996_);
v___x_16726__boxed_4021_ = lean_unbox(v___x_3997_);
v_res_4022_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_3988_, v_tail_3989_, v_params_3990_, v___x_3991_, v_numIndices_3992_, v___x_3993_, v___x_3994_, v___x_16724__boxed_4019_, v___x_16725__boxed_4020_, v___x_16726__boxed_4021_, v_is_3998_, v___x_3999_, v___x_4000_, v___x_4001_, v___x_4002_, v___x_4003_, v___x_4004_, v_heq_4005_, v_val_4006_, v___x_4007_, v_declName_4008_, v_levelParams_4009_, v___x_4010_, v_numParams_4011_, v___x_4012_, v_motive_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4023_, lean_object* v___x_4024_, lean_object* v_is_4025_, lean_object* v_head_4026_, lean_object* v_ctors_4027_, lean_object* v_tail_4028_, lean_object* v_params_4029_, lean_object* v___x_4030_, lean_object* v_numIndices_4031_, lean_object* v___x_4032_, lean_object* v___x_4033_, lean_object* v___x_4034_, lean_object* v___x_4035_, lean_object* v___x_4036_, lean_object* v_val_4037_, lean_object* v___x_4038_, lean_object* v_declName_4039_, lean_object* v_levelParams_4040_, lean_object* v_numParams_4041_, lean_object* v___x_4042_, lean_object* v_heq_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; uint8_t v___x_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4049_ = lean_unsigned_to_nat(3u);
v___x_4050_ = lean_mk_empty_array_with_capacity(v___x_4049_);
lean_inc_ref(v___x_4023_);
v___x_4051_ = lean_array_push(v___x_4050_, v___x_4023_);
lean_inc_ref(v___x_4024_);
v___x_4052_ = lean_array_push(v___x_4051_, v___x_4024_);
lean_inc_ref(v_heq_4043_);
v___x_4053_ = lean_array_push(v___x_4052_, v_heq_4043_);
lean_inc_ref(v_is_4025_);
v___x_4054_ = l_Array_append___redArg(v_is_4025_, v___x_4053_);
lean_dec_ref(v___x_4053_);
v___x_4055_ = l_Lean_mkSort(v_head_4026_);
v___x_4056_ = 0;
v___x_4057_ = 1;
v___x_4058_ = 1;
v___x_4059_ = l_Lean_Meta_mkForallFVars(v___x_4054_, v___x_4055_, v___x_4056_, v___x_4057_, v___x_4057_, v___x_4058_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref(v___x_4059_);
v___x_4061_ = lean_box(v___x_4056_);
v___x_4062_ = lean_box(v___x_4057_);
v___x_4063_ = lean_box(v___x_4058_);
v___f_4064_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4064_, 0, v_ctors_4027_);
lean_closure_set(v___f_4064_, 1, v_tail_4028_);
lean_closure_set(v___f_4064_, 2, v_params_4029_);
lean_closure_set(v___f_4064_, 3, v___x_4030_);
lean_closure_set(v___f_4064_, 4, v_numIndices_4031_);
lean_closure_set(v___f_4064_, 5, v___x_4032_);
lean_closure_set(v___f_4064_, 6, v___x_4054_);
lean_closure_set(v___f_4064_, 7, v___x_4061_);
lean_closure_set(v___f_4064_, 8, v___x_4062_);
lean_closure_set(v___f_4064_, 9, v___x_4063_);
lean_closure_set(v___f_4064_, 10, v_is_4025_);
lean_closure_set(v___f_4064_, 11, v___x_4024_);
lean_closure_set(v___f_4064_, 12, v___x_4023_);
lean_closure_set(v___f_4064_, 13, v___x_4033_);
lean_closure_set(v___f_4064_, 14, v___x_4034_);
lean_closure_set(v___f_4064_, 15, v___x_4035_);
lean_closure_set(v___f_4064_, 16, v___x_4036_);
lean_closure_set(v___f_4064_, 17, v_heq_4043_);
lean_closure_set(v___f_4064_, 18, v_val_4037_);
lean_closure_set(v___f_4064_, 19, v___x_4038_);
lean_closure_set(v___f_4064_, 20, v_declName_4039_);
lean_closure_set(v___f_4064_, 21, v_levelParams_4040_);
lean_closure_set(v___f_4064_, 22, v___x_4049_);
lean_closure_set(v___f_4064_, 23, v_numParams_4041_);
lean_closure_set(v___f_4064_, 24, v___x_4042_);
v___x_4065_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4066_ = 0;
v___x_4067_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4065_, v___x_4058_, v_a_4060_, v___f_4064_, v___x_4066_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
return v___x_4067_;
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec_ref(v___x_4054_);
lean_dec_ref(v_heq_4043_);
lean_dec_ref(v___x_4042_);
lean_dec(v_numParams_4041_);
lean_dec(v_levelParams_4040_);
lean_dec(v_declName_4039_);
lean_dec_ref(v___x_4038_);
lean_dec_ref(v_val_4037_);
lean_dec_ref(v___x_4036_);
lean_dec_ref(v___x_4035_);
lean_dec(v___x_4034_);
lean_dec(v___x_4033_);
lean_dec(v___x_4032_);
lean_dec(v_numIndices_4031_);
lean_dec(v___x_4030_);
lean_dec_ref(v_params_4029_);
lean_dec(v_tail_4028_);
lean_dec(v_ctors_4027_);
lean_dec_ref(v_is_4025_);
lean_dec_ref(v___x_4024_);
lean_dec_ref(v___x_4023_);
v_a_4068_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4059_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4059_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4076_ = _args[0];
lean_object* v___x_4077_ = _args[1];
lean_object* v_is_4078_ = _args[2];
lean_object* v_head_4079_ = _args[3];
lean_object* v_ctors_4080_ = _args[4];
lean_object* v_tail_4081_ = _args[5];
lean_object* v_params_4082_ = _args[6];
lean_object* v___x_4083_ = _args[7];
lean_object* v_numIndices_4084_ = _args[8];
lean_object* v___x_4085_ = _args[9];
lean_object* v___x_4086_ = _args[10];
lean_object* v___x_4087_ = _args[11];
lean_object* v___x_4088_ = _args[12];
lean_object* v___x_4089_ = _args[13];
lean_object* v_val_4090_ = _args[14];
lean_object* v___x_4091_ = _args[15];
lean_object* v_declName_4092_ = _args[16];
lean_object* v_levelParams_4093_ = _args[17];
lean_object* v_numParams_4094_ = _args[18];
lean_object* v___x_4095_ = _args[19];
lean_object* v_heq_4096_ = _args[20];
lean_object* v___y_4097_ = _args[21];
lean_object* v___y_4098_ = _args[22];
lean_object* v___y_4099_ = _args[23];
lean_object* v___y_4100_ = _args[24];
lean_object* v___y_4101_ = _args[25];
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4076_, v___x_4077_, v_is_4078_, v_head_4079_, v_ctors_4080_, v_tail_4081_, v_params_4082_, v___x_4083_, v_numIndices_4084_, v___x_4085_, v___x_4086_, v___x_4087_, v___x_4088_, v___x_4089_, v_val_4090_, v___x_4091_, v_declName_4092_, v_levelParams_4093_, v_numParams_4094_, v___x_4095_, v_heq_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4103_, lean_object* v_x1_4104_, lean_object* v_indName_4105_, lean_object* v_tail_4106_, lean_object* v_params_4107_, lean_object* v_is_4108_, lean_object* v___x_4109_, lean_object* v_head_4110_, lean_object* v_ctors_4111_, lean_object* v_numIndices_4112_, lean_object* v___x_4113_, lean_object* v___x_4114_, lean_object* v_val_4115_, lean_object* v_declName_4116_, lean_object* v_levelParams_4117_, lean_object* v_numParams_4118_, lean_object* v___x_4119_, lean_object* v_x2_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = lean_array_get_borrowed(v___x_4103_, v_x1_4104_, v___x_4127_);
v___x_4129_ = lean_array_get_borrowed(v___x_4103_, v_x2_4120_, v___x_4127_);
v___x_4130_ = l_mkCtorIdxName(v_indName_4105_);
lean_inc(v_tail_4106_);
v___x_4131_ = l_Lean_mkConst(v___x_4130_, v_tail_4106_);
lean_inc_ref(v_params_4107_);
v___x_4132_ = l_Array_append___redArg(v_params_4107_, v_is_4108_);
v___x_4133_ = lean_mk_empty_array_with_capacity(v___x_4109_);
lean_inc(v___x_4128_);
lean_inc_ref_n(v___x_4133_, 2);
v___x_4134_ = lean_array_push(v___x_4133_, v___x_4128_);
lean_inc_ref(v___x_4132_);
v___x_4135_ = l_Array_append___redArg(v___x_4132_, v___x_4134_);
lean_inc_ref(v___x_4131_);
v___x_4136_ = l_Lean_mkAppN(v___x_4131_, v___x_4135_);
lean_dec_ref(v___x_4135_);
lean_inc(v___x_4129_);
v___x_4137_ = lean_array_push(v___x_4133_, v___x_4129_);
v___x_4138_ = l_Array_append___redArg(v___x_4132_, v___x_4137_);
v___x_4139_ = l_Lean_mkAppN(v___x_4131_, v___x_4138_);
lean_dec_ref(v___x_4138_);
v___x_4140_ = l_Lean_Meta_mkEq(v___x_4136_, v___x_4139_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___f_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref(v___x_4140_);
lean_inc(v___x_4129_);
lean_inc(v___x_4128_);
v___f_4142_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4142_, 0, v___x_4128_);
lean_closure_set(v___f_4142_, 1, v___x_4129_);
lean_closure_set(v___f_4142_, 2, v_is_4108_);
lean_closure_set(v___f_4142_, 3, v_head_4110_);
lean_closure_set(v___f_4142_, 4, v_ctors_4111_);
lean_closure_set(v___f_4142_, 5, v_tail_4106_);
lean_closure_set(v___f_4142_, 6, v_params_4107_);
lean_closure_set(v___f_4142_, 7, v___x_4127_);
lean_closure_set(v___f_4142_, 8, v_numIndices_4112_);
lean_closure_set(v___f_4142_, 9, v___x_4109_);
lean_closure_set(v___f_4142_, 10, v___x_4113_);
lean_closure_set(v___f_4142_, 11, v___x_4114_);
lean_closure_set(v___f_4142_, 12, v___x_4134_);
lean_closure_set(v___f_4142_, 13, v___x_4137_);
lean_closure_set(v___f_4142_, 14, v_val_4115_);
lean_closure_set(v___f_4142_, 15, v___x_4133_);
lean_closure_set(v___f_4142_, 16, v_declName_4116_);
lean_closure_set(v___f_4142_, 17, v_levelParams_4117_);
lean_closure_set(v___f_4142_, 18, v_numParams_4118_);
lean_closure_set(v___f_4142_, 19, v___x_4119_);
v___x_4143_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4144_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4143_, v_a_4141_, v___f_4142_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4134_);
lean_dec_ref(v___x_4133_);
lean_dec_ref(v___x_4119_);
lean_dec(v_numParams_4118_);
lean_dec(v_levelParams_4117_);
lean_dec(v_declName_4116_);
lean_dec_ref(v_val_4115_);
lean_dec(v___x_4114_);
lean_dec(v___x_4113_);
lean_dec(v_numIndices_4112_);
lean_dec(v_ctors_4111_);
lean_dec(v_head_4110_);
lean_dec(v___x_4109_);
lean_dec_ref(v_is_4108_);
lean_dec_ref(v_params_4107_);
lean_dec(v_tail_4106_);
v_a_4145_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4140_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4140_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4153_ = _args[0];
lean_object* v_x1_4154_ = _args[1];
lean_object* v_indName_4155_ = _args[2];
lean_object* v_tail_4156_ = _args[3];
lean_object* v_params_4157_ = _args[4];
lean_object* v_is_4158_ = _args[5];
lean_object* v___x_4159_ = _args[6];
lean_object* v_head_4160_ = _args[7];
lean_object* v_ctors_4161_ = _args[8];
lean_object* v_numIndices_4162_ = _args[9];
lean_object* v___x_4163_ = _args[10];
lean_object* v___x_4164_ = _args[11];
lean_object* v_val_4165_ = _args[12];
lean_object* v_declName_4166_ = _args[13];
lean_object* v_levelParams_4167_ = _args[14];
lean_object* v_numParams_4168_ = _args[15];
lean_object* v___x_4169_ = _args[16];
lean_object* v_x2_4170_ = _args[17];
lean_object* v_x_4171_ = _args[18];
lean_object* v___y_4172_ = _args[19];
lean_object* v___y_4173_ = _args[20];
lean_object* v___y_4174_ = _args[21];
lean_object* v___y_4175_ = _args[22];
lean_object* v___y_4176_ = _args[23];
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4153_, v_x1_4154_, v_indName_4155_, v_tail_4156_, v_params_4157_, v_is_4158_, v___x_4159_, v_head_4160_, v_ctors_4161_, v_numIndices_4162_, v___x_4163_, v___x_4164_, v_val_4165_, v_declName_4166_, v_levelParams_4167_, v_numParams_4168_, v___x_4169_, v_x2_4170_, v_x_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_x_4171_);
lean_dec_ref(v_x2_4170_);
lean_dec_ref(v_x1_4154_);
lean_dec_ref(v___x_4153_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4178_, lean_object* v_indName_4179_, lean_object* v_tail_4180_, lean_object* v_params_4181_, lean_object* v_is_4182_, lean_object* v___x_4183_, lean_object* v_head_4184_, lean_object* v_ctors_4185_, lean_object* v_numIndices_4186_, lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v_val_4189_, lean_object* v_declName_4190_, lean_object* v_levelParams_4191_, lean_object* v_numParams_4192_, lean_object* v___x_4193_, lean_object* v_t_4194_, lean_object* v___x_4195_, lean_object* v_x1_4196_, lean_object* v_x_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___f_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; 
v___f_4203_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4203_, 0, v___x_4178_);
lean_closure_set(v___f_4203_, 1, v_x1_4196_);
lean_closure_set(v___f_4203_, 2, v_indName_4179_);
lean_closure_set(v___f_4203_, 3, v_tail_4180_);
lean_closure_set(v___f_4203_, 4, v_params_4181_);
lean_closure_set(v___f_4203_, 5, v_is_4182_);
lean_closure_set(v___f_4203_, 6, v___x_4183_);
lean_closure_set(v___f_4203_, 7, v_head_4184_);
lean_closure_set(v___f_4203_, 8, v_ctors_4185_);
lean_closure_set(v___f_4203_, 9, v_numIndices_4186_);
lean_closure_set(v___f_4203_, 10, v___x_4187_);
lean_closure_set(v___f_4203_, 11, v___x_4188_);
lean_closure_set(v___f_4203_, 12, v_val_4189_);
lean_closure_set(v___f_4203_, 13, v_declName_4190_);
lean_closure_set(v___f_4203_, 14, v_levelParams_4191_);
lean_closure_set(v___f_4203_, 15, v_numParams_4192_);
lean_closure_set(v___f_4203_, 16, v___x_4193_);
v___x_4204_ = 0;
v___x_4205_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4194_, v___x_4195_, v___f_4203_, v___x_4204_, v___x_4204_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4206_ = _args[0];
lean_object* v_indName_4207_ = _args[1];
lean_object* v_tail_4208_ = _args[2];
lean_object* v_params_4209_ = _args[3];
lean_object* v_is_4210_ = _args[4];
lean_object* v___x_4211_ = _args[5];
lean_object* v_head_4212_ = _args[6];
lean_object* v_ctors_4213_ = _args[7];
lean_object* v_numIndices_4214_ = _args[8];
lean_object* v___x_4215_ = _args[9];
lean_object* v___x_4216_ = _args[10];
lean_object* v_val_4217_ = _args[11];
lean_object* v_declName_4218_ = _args[12];
lean_object* v_levelParams_4219_ = _args[13];
lean_object* v_numParams_4220_ = _args[14];
lean_object* v___x_4221_ = _args[15];
lean_object* v_t_4222_ = _args[16];
lean_object* v___x_4223_ = _args[17];
lean_object* v_x1_4224_ = _args[18];
lean_object* v_x_4225_ = _args[19];
lean_object* v___y_4226_ = _args[20];
lean_object* v___y_4227_ = _args[21];
lean_object* v___y_4228_ = _args[22];
lean_object* v___y_4229_ = _args[23];
lean_object* v___y_4230_ = _args[24];
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4206_, v_indName_4207_, v_tail_4208_, v_params_4209_, v_is_4210_, v___x_4211_, v_head_4212_, v_ctors_4213_, v_numIndices_4214_, v___x_4215_, v___x_4216_, v_val_4217_, v_declName_4218_, v_levelParams_4219_, v_numParams_4220_, v___x_4221_, v_t_4222_, v___x_4223_, v_x1_4224_, v_x_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_x_4225_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4232_, lean_object* v_indName_4233_, lean_object* v_tail_4234_, lean_object* v_params_4235_, lean_object* v_head_4236_, lean_object* v_ctors_4237_, lean_object* v_numIndices_4238_, lean_object* v___x_4239_, lean_object* v___x_4240_, lean_object* v_val_4241_, lean_object* v_declName_4242_, lean_object* v_levelParams_4243_, lean_object* v_numParams_4244_, lean_object* v___x_4245_, lean_object* v_is_4246_, lean_object* v_t_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___f_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; 
v___x_4253_ = lean_unsigned_to_nat(1u);
v___x_4254_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4247_);
v___f_4255_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4255_, 0, v___x_4232_);
lean_closure_set(v___f_4255_, 1, v_indName_4233_);
lean_closure_set(v___f_4255_, 2, v_tail_4234_);
lean_closure_set(v___f_4255_, 3, v_params_4235_);
lean_closure_set(v___f_4255_, 4, v_is_4246_);
lean_closure_set(v___f_4255_, 5, v___x_4253_);
lean_closure_set(v___f_4255_, 6, v_head_4236_);
lean_closure_set(v___f_4255_, 7, v_ctors_4237_);
lean_closure_set(v___f_4255_, 8, v_numIndices_4238_);
lean_closure_set(v___f_4255_, 9, v___x_4239_);
lean_closure_set(v___f_4255_, 10, v___x_4240_);
lean_closure_set(v___f_4255_, 11, v_val_4241_);
lean_closure_set(v___f_4255_, 12, v_declName_4242_);
lean_closure_set(v___f_4255_, 13, v_levelParams_4243_);
lean_closure_set(v___f_4255_, 14, v_numParams_4244_);
lean_closure_set(v___f_4255_, 15, v___x_4245_);
lean_closure_set(v___f_4255_, 16, v_t_4247_);
lean_closure_set(v___f_4255_, 17, v___x_4254_);
v___x_4256_ = 0;
v___x_4257_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4247_, v___x_4254_, v___f_4255_, v___x_4256_, v___x_4256_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4258_ = _args[0];
lean_object* v_indName_4259_ = _args[1];
lean_object* v_tail_4260_ = _args[2];
lean_object* v_params_4261_ = _args[3];
lean_object* v_head_4262_ = _args[4];
lean_object* v_ctors_4263_ = _args[5];
lean_object* v_numIndices_4264_ = _args[6];
lean_object* v___x_4265_ = _args[7];
lean_object* v___x_4266_ = _args[8];
lean_object* v_val_4267_ = _args[9];
lean_object* v_declName_4268_ = _args[10];
lean_object* v_levelParams_4269_ = _args[11];
lean_object* v_numParams_4270_ = _args[12];
lean_object* v___x_4271_ = _args[13];
lean_object* v_is_4272_ = _args[14];
lean_object* v_t_4273_ = _args[15];
lean_object* v___y_4274_ = _args[16];
lean_object* v___y_4275_ = _args[17];
lean_object* v___y_4276_ = _args[18];
lean_object* v___y_4277_ = _args[19];
lean_object* v___y_4278_ = _args[20];
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4258_, v_indName_4259_, v_tail_4260_, v_params_4261_, v_head_4262_, v_ctors_4263_, v_numIndices_4264_, v___x_4265_, v___x_4266_, v_val_4267_, v_declName_4268_, v_levelParams_4269_, v_numParams_4270_, v___x_4271_, v_is_4272_, v_t_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4280_, lean_object* v_indName_4281_, lean_object* v_tail_4282_, lean_object* v_head_4283_, lean_object* v_ctors_4284_, lean_object* v_numIndices_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v_val_4288_, lean_object* v_declName_4289_, lean_object* v_levelParams_4290_, lean_object* v_numParams_4291_, lean_object* v_params_4292_, lean_object* v_t_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; lean_object* v___f_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; lean_object* v___x_4303_; 
v___x_4299_ = l_Lean_Expr_bindingBody_x21(v_t_4293_);
lean_inc_ref(v___x_4299_);
lean_inc(v_numIndices_4285_);
v___f_4300_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4300_, 0, v___x_4280_);
lean_closure_set(v___f_4300_, 1, v_indName_4281_);
lean_closure_set(v___f_4300_, 2, v_tail_4282_);
lean_closure_set(v___f_4300_, 3, v_params_4292_);
lean_closure_set(v___f_4300_, 4, v_head_4283_);
lean_closure_set(v___f_4300_, 5, v_ctors_4284_);
lean_closure_set(v___f_4300_, 6, v_numIndices_4285_);
lean_closure_set(v___f_4300_, 7, v___x_4286_);
lean_closure_set(v___f_4300_, 8, v___x_4287_);
lean_closure_set(v___f_4300_, 9, v_val_4288_);
lean_closure_set(v___f_4300_, 10, v_declName_4289_);
lean_closure_set(v___f_4300_, 11, v_levelParams_4290_);
lean_closure_set(v___f_4300_, 12, v_numParams_4291_);
lean_closure_set(v___f_4300_, 13, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4301_, 0, v_numIndices_4285_);
v___x_4302_ = 0;
v___x_4303_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4299_, v___x_4301_, v___f_4300_, v___x_4302_, v___x_4302_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4304_ = _args[0];
lean_object* v_indName_4305_ = _args[1];
lean_object* v_tail_4306_ = _args[2];
lean_object* v_head_4307_ = _args[3];
lean_object* v_ctors_4308_ = _args[4];
lean_object* v_numIndices_4309_ = _args[5];
lean_object* v___x_4310_ = _args[6];
lean_object* v___x_4311_ = _args[7];
lean_object* v_val_4312_ = _args[8];
lean_object* v_declName_4313_ = _args[9];
lean_object* v_levelParams_4314_ = _args[10];
lean_object* v_numParams_4315_ = _args[11];
lean_object* v_params_4316_ = _args[12];
lean_object* v_t_4317_ = _args[13];
lean_object* v___y_4318_ = _args[14];
lean_object* v___y_4319_ = _args[15];
lean_object* v___y_4320_ = _args[16];
lean_object* v___y_4321_ = _args[17];
lean_object* v___y_4322_ = _args[18];
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4304_, v_indName_4305_, v_tail_4306_, v_head_4307_, v_ctors_4308_, v_numIndices_4309_, v___x_4310_, v___x_4311_, v_val_4312_, v_declName_4313_, v_levelParams_4314_, v_numParams_4315_, v_params_4316_, v_t_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec_ref(v_t_4317_);
return v_res_4323_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4328_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4329_ = lean_unsigned_to_nat(58u);
v___x_4330_ = lean_unsigned_to_nat(142u);
v___x_4331_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4332_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4333_ = l_mkPanicMessageWithDecl(v___x_4332_, v___x_4331_, v___x_4330_, v___x_4329_, v___x_4328_);
return v___x_4333_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4334_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4335_ = lean_unsigned_to_nat(60u);
v___x_4336_ = lean_unsigned_to_nat(136u);
v___x_4337_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4338_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4339_ = l_mkPanicMessageWithDecl(v___x_4338_, v___x_4337_, v___x_4336_, v___x_4335_, v___x_4334_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4340_, lean_object* v_indName_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v___x_4347_; 
lean_inc(v_indName_4341_);
v___x_4347_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref(v___x_4347_);
if (lean_obj_tag(v_a_4348_) == 5)
{
lean_object* v_val_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_val_4349_ = lean_ctor_get(v_a_4348_, 0);
lean_inc_ref(v_val_4349_);
lean_dec_ref(v_a_4348_);
v___x_4350_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4340_);
v___x_4351_ = l_Lean_Name_append(v_declName_4340_, v___x_4350_);
lean_inc(v_indName_4341_);
lean_inc(v___x_4351_);
v___x_4352_ = l_Lean_mkCasesOnSameCtorHet(v___x_4351_, v_indName_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4385_; 
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4385_ == 0)
{
lean_object* v_unused_4386_; 
v_unused_4386_ = lean_ctor_get(v___x_4352_, 0);
lean_dec(v_unused_4386_);
v___x_4354_ = v___x_4352_;
v_isShared_4355_ = v_isSharedCheck_4385_;
goto v_resetjp_4353_;
}
else
{
lean_dec(v___x_4352_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4385_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
lean_inc(v_indName_4341_);
v___x_4356_ = l_Lean_mkCasesOnName(v_indName_4341_);
v___x_4357_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4356_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v_levelParams_4359_; lean_object* v_type_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref(v___x_4357_);
v_levelParams_4359_ = lean_ctor_get(v_a_4358_, 1);
lean_inc_n(v_levelParams_4359_, 2);
v_type_4360_ = lean_ctor_get(v_a_4358_, 2);
lean_inc_ref(v_type_4360_);
lean_dec(v_a_4358_);
v___x_4361_ = lean_box(0);
v___x_4362_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4359_, v___x_4361_);
if (lean_obj_tag(v___x_4362_) == 1)
{
lean_object* v_head_4363_; lean_object* v_tail_4364_; lean_object* v_numParams_4365_; lean_object* v_numIndices_4366_; lean_object* v_ctors_4367_; lean_object* v___x_4368_; lean_object* v___f_4369_; lean_object* v___x_4371_; 
v_head_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_head_4363_);
v_tail_4364_ = lean_ctor_get(v___x_4362_, 1);
lean_inc(v_tail_4364_);
v_numParams_4365_ = lean_ctor_get(v_val_4349_, 1);
lean_inc_n(v_numParams_4365_, 2);
v_numIndices_4366_ = lean_ctor_get(v_val_4349_, 2);
lean_inc(v_numIndices_4366_);
v_ctors_4367_ = lean_ctor_get(v_val_4349_, 4);
lean_inc(v_ctors_4367_);
v___x_4368_ = l_Lean_instInhabitedExpr;
v___f_4369_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4369_, 0, v___x_4368_);
lean_closure_set(v___f_4369_, 1, v_indName_4341_);
lean_closure_set(v___f_4369_, 2, v_tail_4364_);
lean_closure_set(v___f_4369_, 3, v_head_4363_);
lean_closure_set(v___f_4369_, 4, v_ctors_4367_);
lean_closure_set(v___f_4369_, 5, v_numIndices_4366_);
lean_closure_set(v___f_4369_, 6, v___x_4351_);
lean_closure_set(v___f_4369_, 7, v___x_4362_);
lean_closure_set(v___f_4369_, 8, v_val_4349_);
lean_closure_set(v___f_4369_, 9, v_declName_4340_);
lean_closure_set(v___f_4369_, 10, v_levelParams_4359_);
lean_closure_set(v___f_4369_, 11, v_numParams_4365_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set_tag(v___x_4354_, 1);
lean_ctor_set(v___x_4354_, 0, v_numParams_4365_);
v___x_4371_ = v___x_4354_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_numParams_4365_);
v___x_4371_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
uint8_t v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = 0;
v___x_4373_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4360_, v___x_4371_, v___f_4369_, v___x_4372_, v___x_4372_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
return v___x_4373_;
}
}
else
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
lean_dec(v___x_4362_);
lean_dec_ref(v_type_4360_);
lean_dec(v_levelParams_4359_);
lean_del_object(v___x_4354_);
lean_dec(v___x_4351_);
lean_dec_ref(v_val_4349_);
lean_dec(v_indName_4341_);
lean_dec(v_declName_4340_);
v___x_4375_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4376_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4375_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
return v___x_4376_;
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_del_object(v___x_4354_);
lean_dec(v___x_4351_);
lean_dec_ref(v_val_4349_);
lean_dec(v_indName_4341_);
lean_dec(v_declName_4340_);
v_a_4377_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4357_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4357_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
else
{
lean_dec(v___x_4351_);
lean_dec_ref(v_val_4349_);
lean_dec(v_indName_4341_);
lean_dec(v_declName_4340_);
return v___x_4352_;
}
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
lean_dec(v_a_4348_);
lean_dec(v_indName_4341_);
lean_dec(v_declName_4340_);
v___x_4387_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4388_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4387_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
return v___x_4388_;
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_indName_4341_);
lean_dec(v_declName_4340_);
v_a_4389_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4347_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4347_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4397_, lean_object* v_indName_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_mkCasesOnSameCtor(v_declName_4397_, v_indName_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4405_, lean_object* v_params_4406_, lean_object* v_motive_4407_, lean_object* v_as_4408_, lean_object* v_i_4409_, lean_object* v_j_4410_, lean_object* v_inv_4411_, lean_object* v_bs_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4405_, v_params_4406_, v_motive_4407_, v_as_4408_, v_i_4409_, v_j_4410_, v_bs_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4419_, lean_object* v_params_4420_, lean_object* v_motive_4421_, lean_object* v_as_4422_, lean_object* v_i_4423_, lean_object* v_j_4424_, lean_object* v_inv_4425_, lean_object* v_bs_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4419_, v_params_4420_, v_motive_4421_, v_as_4422_, v_i_4423_, v_j_4424_, v_inv_4425_, v_bs_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v_as_4422_);
lean_dec_ref(v_params_4420_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4433_, lean_object* v_params_4434_, lean_object* v_a_4435_, lean_object* v_snd_4436_, lean_object* v_alts_4437_, lean_object* v_as_4438_, lean_object* v_i_4439_, lean_object* v_j_4440_, lean_object* v_inv_4441_, lean_object* v_bs_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4433_, v_params_4434_, v_a_4435_, v_snd_4436_, v_alts_4437_, v_as_4438_, v_i_4439_, v_j_4440_, v_bs_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4449_, lean_object* v_params_4450_, lean_object* v_a_4451_, lean_object* v_snd_4452_, lean_object* v_alts_4453_, lean_object* v_as_4454_, lean_object* v_i_4455_, lean_object* v_j_4456_, lean_object* v_inv_4457_, lean_object* v_bs_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4449_, v_params_4450_, v_a_4451_, v_snd_4452_, v_alts_4453_, v_as_4454_, v_i_4455_, v_j_4456_, v_inv_4457_, v_bs_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec_ref(v_as_4454_);
lean_dec_ref(v_params_4450_);
return v_res_4464_;
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
