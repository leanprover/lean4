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
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
static const lean_closure_object l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "could not apply "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " to close\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unifyEqns\? unexpectedly closed goal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_235_; uint8_t v___y_237_; lean_object* v_env_245_; uint8_t v___x_246_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_env_245_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref_n(v_env_245_, 2);
lean_dec(v___x_235_);
v___x_246_ = l_Lean_Environment_hasUnsafe(v_env_245_, v_type_230_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_Environment_hasUnsafe(v_env_245_, v_value_231_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 1;
v___y_237_ = v___x_248_;
goto v___jp_236_;
}
else
{
goto v___jp_243_;
}
}
else
{
lean_dec_ref(v_env_245_);
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
uint8_t v___x_244_; 
v___x_244_ = 0;
v___y_237_ = v___x_244_;
goto v___jp_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object* v_name_249_, lean_object* v_levelParams_250_, lean_object* v_type_251_, lean_object* v_value_252_, lean_object* v_hints_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_249_, v_levelParams_250_, v_type_251_, v_value_252_, v_hints_253_, v___y_254_);
lean_dec(v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object* v_name_257_, lean_object* v_levelParams_258_, lean_object* v_type_259_, lean_object* v_value_260_, lean_object* v_hints_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_257_, v_levelParams_258_, v_type_259_, v_value_260_, v_hints_261_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object* v_name_268_, lean_object* v_levelParams_269_, lean_object* v_type_270_, lean_object* v_value_271_, lean_object* v_hints_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_268_, v_levelParams_269_, v_type_270_, v_value_271_, v_hints_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___f_286_; lean_object* v___x_16193__overap_287_; lean_object* v___x_288_; 
v___f_286_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0));
v___x_16193__overap_287_ = lean_panic_fn_borrowed(v___f_286_, v_msg_280_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
v___x_288_ = lean_apply_5(v___x_16193__overap_287_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___boxed(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_296_, lean_object* v_type_297_, lean_object* v_k_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = 0;
v___x_305_ = 0;
v___x_306_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_296_, v___x_304_, v_type_297_, v_k_298_, v___x_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_307_, lean_object* v_type_308_, lean_object* v_k_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_307_, v_type_308_, v_k_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_316_, lean_object* v_ism2_317_, lean_object* v_motive_318_, uint8_t v___x_319_, uint8_t v___x_320_, uint8_t v___x_321_, lean_object* v_a_322_, lean_object* v___f_323_, lean_object* v_zs1_324_, lean_object* v_val_325_, lean_object* v___x_326_, lean_object* v_indName_327_, lean_object* v_v_328_, lean_object* v___x_329_, lean_object* v_params_330_, lean_object* v___x_331_, lean_object* v_h_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Array_append___redArg(v___x_316_, v_ism2_317_);
v___x_339_ = l_Lean_mkAppN(v_motive_318_, v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_Meta_mkLambdaFVars(v_ism2_317_, v___x_339_, v___x_319_, v___x_320_, v___x_319_, v___x_320_, v___x_321_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_322_, v___f_323_, v___x_319_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___y_345_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_348_ = l_Lean_InductiveVal_numCtors(v_val_325_);
v___x_349_ = lean_nat_dec_eq(v___x_348_, v___x_326_);
lean_dec(v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_331_);
v___x_350_ = l_Lean_mkConstructorElimName(v_indName_327_, v_v_328_);
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_329_);
v___x_352_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_353_ = lean_array_push(v___x_352_, v_a_341_);
v___x_354_ = l_Array_append___redArg(v_params_330_, v___x_353_);
lean_dec_ref(v___x_353_);
v___x_355_ = l_Array_append___redArg(v___x_354_, v_ism2_317_);
v___x_356_ = lean_unsigned_to_nat(2u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
lean_inc_ref(v_h_332_);
v___x_358_ = lean_array_push(v___x_357_, v_h_332_);
v___x_359_ = lean_array_push(v___x_358_, v_a_343_);
v___x_360_ = l_Array_append___redArg(v___x_355_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = l_Lean_mkAppN(v___x_351_, v___x_360_);
lean_dec_ref(v___x_360_);
v___y_345_ = v___x_361_;
goto v___jp_344_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_v_328_);
lean_dec(v_indName_327_);
v___x_362_ = l_Lean_mkConst(v___x_331_, v___x_329_);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_326_);
lean_inc_ref(v___x_363_);
v___x_364_ = lean_array_push(v___x_363_, v_a_341_);
v___x_365_ = l_Array_append___redArg(v_params_330_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = l_Array_append___redArg(v___x_365_, v_ism2_317_);
v___x_367_ = lean_array_push(v___x_363_, v_a_343_);
v___x_368_ = l_Array_append___redArg(v___x_366_, v___x_367_);
lean_dec_ref(v___x_367_);
v___x_369_ = l_Lean_mkAppN(v___x_362_, v___x_368_);
lean_dec_ref(v___x_368_);
v___y_345_ = v___x_369_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_array_push(v_zs1_324_, v_h_332_);
v___x_347_ = l_Lean_Meta_mkLambdaFVars(v___x_346_, v___y_345_, v___x_319_, v___x_320_, v___x_319_, v___x_320_, v___x_321_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec_ref(v___x_346_);
return v___x_347_;
}
}
else
{
lean_dec(v_a_341_);
lean_dec_ref(v_h_332_);
lean_dec(v___x_331_);
lean_dec_ref(v_params_330_);
lean_dec(v___x_329_);
lean_dec(v_v_328_);
lean_dec(v_indName_327_);
lean_dec_ref(v_zs1_324_);
return v___x_342_;
}
}
else
{
lean_dec_ref(v_h_332_);
lean_dec(v___x_331_);
lean_dec_ref(v_params_330_);
lean_dec(v___x_329_);
lean_dec(v_v_328_);
lean_dec(v_indName_327_);
lean_dec_ref(v_zs1_324_);
lean_dec_ref(v___f_323_);
lean_dec_ref(v_a_322_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_370_ = _args[0];
lean_object* v_ism2_371_ = _args[1];
lean_object* v_motive_372_ = _args[2];
lean_object* v___x_373_ = _args[3];
lean_object* v___x_374_ = _args[4];
lean_object* v___x_375_ = _args[5];
lean_object* v_a_376_ = _args[6];
lean_object* v___f_377_ = _args[7];
lean_object* v_zs1_378_ = _args[8];
lean_object* v_val_379_ = _args[9];
lean_object* v___x_380_ = _args[10];
lean_object* v_indName_381_ = _args[11];
lean_object* v_v_382_ = _args[12];
lean_object* v___x_383_ = _args[13];
lean_object* v_params_384_ = _args[14];
lean_object* v___x_385_ = _args[15];
lean_object* v_h_386_ = _args[16];
lean_object* v___y_387_ = _args[17];
lean_object* v___y_388_ = _args[18];
lean_object* v___y_389_ = _args[19];
lean_object* v___y_390_ = _args[20];
lean_object* v___y_391_ = _args[21];
_start:
{
uint8_t v___x_21097__boxed_392_; uint8_t v___x_21098__boxed_393_; uint8_t v___x_21099__boxed_394_; lean_object* v_res_395_; 
v___x_21097__boxed_392_ = lean_unbox(v___x_373_);
v___x_21098__boxed_393_ = lean_unbox(v___x_374_);
v___x_21099__boxed_394_ = lean_unbox(v___x_375_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_370_, v_ism2_371_, v_motive_372_, v___x_21097__boxed_392_, v___x_21098__boxed_393_, v___x_21099__boxed_394_, v_a_376_, v___f_377_, v_zs1_378_, v_val_379_, v___x_380_, v_indName_381_, v_v_382_, v___x_383_, v_params_384_, v___x_385_, v_h_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___x_380_);
lean_dec_ref(v_val_379_);
lean_dec_ref(v_ism2_371_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_396_, lean_object* v_alts_397_, lean_object* v___x_398_, lean_object* v_zs1_399_, uint8_t v___x_400_, uint8_t v___x_401_, uint8_t v___x_402_, lean_object* v_zs2_403_, lean_object* v_x_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_410_ = lean_array_get_borrowed(v___x_396_, v_alts_397_, v___x_398_);
v___x_411_ = l_Array_append___redArg(v_zs1_399_, v_zs2_403_);
lean_inc(v___x_410_);
v___x_412_ = l_Lean_mkAppN(v___x_410_, v___x_411_);
lean_dec_ref(v___x_411_);
v___x_413_ = l_Lean_Meta_mkLambdaFVars(v_zs2_403_, v___x_412_, v___x_400_, v___x_401_, v___x_400_, v___x_401_, v___x_402_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_414_, lean_object* v_alts_415_, lean_object* v___x_416_, lean_object* v_zs1_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_zs2_421_, lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_21209__boxed_428_; uint8_t v___x_21210__boxed_429_; uint8_t v___x_21211__boxed_430_; lean_object* v_res_431_; 
v___x_21209__boxed_428_ = lean_unbox(v___x_418_);
v___x_21210__boxed_429_ = lean_unbox(v___x_419_);
v___x_21211__boxed_430_ = lean_unbox(v___x_420_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_414_, v_alts_415_, v___x_416_, v_zs1_417_, v___x_21209__boxed_428_, v___x_21210__boxed_429_, v___x_21211__boxed_430_, v_zs2_421_, v_x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec_ref(v_x_422_);
lean_dec_ref(v_zs2_421_);
lean_dec(v___x_416_);
lean_dec_ref(v_alts_415_);
lean_dec_ref(v___x_414_);
return v_res_431_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_432_; lean_object* v_dummy_433_; 
v___x_432_ = lean_box(0);
v_dummy_433_ = l_Lean_Expr_sort___override(v___x_432_);
return v_dummy_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_442_ = l_Lean_mkConst(v___x_441_, v___x_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_443_, lean_object* v_alts_444_, lean_object* v___x_445_, uint8_t v___x_446_, uint8_t v___x_447_, uint8_t v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v_ism2_452_, lean_object* v_motive_453_, lean_object* v_a_454_, lean_object* v_val_455_, lean_object* v_indName_456_, lean_object* v_v_457_, lean_object* v___x_458_, lean_object* v_params_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_zs1_463_, lean_object* v_ctorRet1_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_470_ = lean_box(v___x_446_);
v___x_471_ = lean_box(v___x_447_);
v___x_472_ = lean_box(v___x_448_);
lean_inc_ref(v_zs1_463_);
lean_inc(v___x_445_);
v___f_473_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_473_, 0, v___x_443_);
lean_closure_set(v___f_473_, 1, v_alts_444_);
lean_closure_set(v___f_473_, 2, v___x_445_);
lean_closure_set(v___f_473_, 3, v_zs1_463_);
lean_closure_set(v___f_473_, 4, v___x_470_);
lean_closure_set(v___f_473_, 5, v___x_471_);
lean_closure_set(v___f_473_, 6, v___x_472_);
v___x_474_ = l_Lean_mkAppN(v___x_449_, v_zs1_463_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
v___x_475_ = lean_whnf(v_ctorRet1_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_dummy_477_; lean_object* v_nargs_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v_dummy_477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_478_ = l_Lean_Expr_getAppNumArgs(v_a_476_);
lean_inc(v_nargs_478_);
v___x_479_ = lean_mk_array(v_nargs_478_, v_dummy_477_);
v___x_480_ = lean_nat_sub(v_nargs_478_, v___x_450_);
lean_dec(v_nargs_478_);
v___x_481_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_476_, v___x_479_, v___x_480_);
v___x_482_ = lean_array_get_size(v___x_481_);
v___x_483_ = l_Array_toSubarray___redArg(v___x_481_, v___x_451_, v___x_482_);
v___x_484_ = l_Subarray_copy___redArg(v___x_483_);
v___x_485_ = lean_array_push(v___x_484_, v___x_474_);
v___x_486_ = lean_box(v___x_446_);
v___x_487_ = lean_box(v___x_447_);
v___x_488_ = lean_box(v___x_448_);
lean_inc(v___x_450_);
v___f_489_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_489_, 0, v___x_485_);
lean_closure_set(v___f_489_, 1, v_ism2_452_);
lean_closure_set(v___f_489_, 2, v_motive_453_);
lean_closure_set(v___f_489_, 3, v___x_486_);
lean_closure_set(v___f_489_, 4, v___x_487_);
lean_closure_set(v___f_489_, 5, v___x_488_);
lean_closure_set(v___f_489_, 6, v_a_454_);
lean_closure_set(v___f_489_, 7, v___f_473_);
lean_closure_set(v___f_489_, 8, v_zs1_463_);
lean_closure_set(v___f_489_, 9, v_val_455_);
lean_closure_set(v___f_489_, 10, v___x_450_);
lean_closure_set(v___f_489_, 11, v_indName_456_);
lean_closure_set(v___f_489_, 12, v_v_457_);
lean_closure_set(v___f_489_, 13, v___x_458_);
lean_closure_set(v___f_489_, 14, v_params_459_);
lean_closure_set(v___f_489_, 15, v___x_460_);
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_491_ = l_Lean_Level_ofNat(v___x_450_);
lean_dec(v___x_450_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_mkConst(v___x_490_, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_496_ = l_Lean_mkRawNatLit(v___x_445_);
v___x_497_ = l_Lean_mkApp3(v___x_494_, v___x_495_, v___x_461_, v___x_496_);
v___x_498_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_462_, v___x_497_, v___f_489_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_498_;
}
else
{
lean_dec_ref(v___x_474_);
lean_dec_ref(v___f_473_);
lean_dec_ref(v_zs1_463_);
lean_dec(v___x_462_);
lean_dec_ref(v___x_461_);
lean_dec(v___x_460_);
lean_dec_ref(v_params_459_);
lean_dec(v___x_458_);
lean_dec(v_v_457_);
lean_dec(v_indName_456_);
lean_dec_ref(v_val_455_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_motive_453_);
lean_dec_ref(v_ism2_452_);
lean_dec(v___x_451_);
lean_dec(v___x_450_);
lean_dec(v___x_445_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_499_ = _args[0];
lean_object* v_alts_500_ = _args[1];
lean_object* v___x_501_ = _args[2];
lean_object* v___x_502_ = _args[3];
lean_object* v___x_503_ = _args[4];
lean_object* v___x_504_ = _args[5];
lean_object* v___x_505_ = _args[6];
lean_object* v___x_506_ = _args[7];
lean_object* v___x_507_ = _args[8];
lean_object* v_ism2_508_ = _args[9];
lean_object* v_motive_509_ = _args[10];
lean_object* v_a_510_ = _args[11];
lean_object* v_val_511_ = _args[12];
lean_object* v_indName_512_ = _args[13];
lean_object* v_v_513_ = _args[14];
lean_object* v___x_514_ = _args[15];
lean_object* v_params_515_ = _args[16];
lean_object* v___x_516_ = _args[17];
lean_object* v___x_517_ = _args[18];
lean_object* v___x_518_ = _args[19];
lean_object* v_zs1_519_ = _args[20];
lean_object* v_ctorRet1_520_ = _args[21];
lean_object* v___y_521_ = _args[22];
lean_object* v___y_522_ = _args[23];
lean_object* v___y_523_ = _args[24];
lean_object* v___y_524_ = _args[25];
lean_object* v___y_525_ = _args[26];
_start:
{
uint8_t v___x_21270__boxed_526_; uint8_t v___x_21271__boxed_527_; uint8_t v___x_21272__boxed_528_; lean_object* v_res_529_; 
v___x_21270__boxed_526_ = lean_unbox(v___x_502_);
v___x_21271__boxed_527_ = lean_unbox(v___x_503_);
v___x_21272__boxed_528_ = lean_unbox(v___x_504_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_499_, v_alts_500_, v___x_501_, v___x_21270__boxed_526_, v___x_21271__boxed_527_, v___x_21272__boxed_528_, v___x_505_, v___x_506_, v___x_507_, v_ism2_508_, v_motive_509_, v_a_510_, v_val_511_, v_indName_512_, v_v_513_, v___x_514_, v_params_515_, v___x_516_, v___x_517_, v___x_518_, v_zs1_519_, v_ctorRet1_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_533_, lean_object* v_params_534_, lean_object* v_alts_535_, lean_object* v___x_536_, lean_object* v_ism2_537_, lean_object* v_motive_538_, lean_object* v_val_539_, lean_object* v_indName_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v___x_543_, size_t v_sz_544_, size_t v_i_545_, lean_object* v_bs_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v___x_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_indName_540_);
lean_dec_ref(v_val_539_);
lean_dec_ref(v_motive_538_);
lean_dec_ref(v_ism2_537_);
lean_dec(v___x_536_);
lean_dec_ref(v_alts_535_);
lean_dec_ref(v_params_534_);
lean_dec(v_tail_533_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_bs_546_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_v_559_; lean_object* v___x_560_; lean_object* v_bs_x27_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_554_ = l_Lean_instInhabitedExpr;
v___x_555_ = 0;
v___x_556_ = 1;
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v_v_559_ = lean_array_uget(v_bs_546_, v_i_545_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_bs_x27_561_ = lean_array_uset(v_bs_546_, v_i_545_, v___x_560_);
v___x_562_ = lean_usize_to_nat(v_i_545_);
lean_inc(v_tail_533_);
lean_inc(v_v_559_);
v___x_563_ = l_Lean_mkConst(v_v_559_, v_tail_533_);
v___x_564_ = l_Lean_mkAppN(v___x_563_, v_params_534_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc_ref(v___x_564_);
v___x_565_ = lean_infer_type(v___x_564_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_n(v_a_566_, 2);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_box(v___x_555_);
v___x_568_ = lean_box(v___x_552_);
v___x_569_ = lean_box(v___x_556_);
lean_inc_ref(v___x_543_);
lean_inc(v___x_542_);
lean_inc_ref(v_params_534_);
lean_inc(v___x_541_);
lean_inc(v_indName_540_);
lean_inc_ref(v_val_539_);
lean_inc_ref(v_motive_538_);
lean_inc_ref(v_ism2_537_);
lean_inc(v___x_536_);
lean_inc_ref(v_alts_535_);
v___f_570_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_570_, 0, v___x_554_);
lean_closure_set(v___f_570_, 1, v_alts_535_);
lean_closure_set(v___f_570_, 2, v___x_562_);
lean_closure_set(v___f_570_, 3, v___x_567_);
lean_closure_set(v___f_570_, 4, v___x_568_);
lean_closure_set(v___f_570_, 5, v___x_569_);
lean_closure_set(v___f_570_, 6, v___x_564_);
lean_closure_set(v___f_570_, 7, v___x_557_);
lean_closure_set(v___f_570_, 8, v___x_536_);
lean_closure_set(v___f_570_, 9, v_ism2_537_);
lean_closure_set(v___f_570_, 10, v_motive_538_);
lean_closure_set(v___f_570_, 11, v_a_566_);
lean_closure_set(v___f_570_, 12, v_val_539_);
lean_closure_set(v___f_570_, 13, v_indName_540_);
lean_closure_set(v___f_570_, 14, v_v_559_);
lean_closure_set(v___f_570_, 15, v___x_541_);
lean_closure_set(v___f_570_, 16, v_params_534_);
lean_closure_set(v___f_570_, 17, v___x_542_);
lean_closure_set(v___f_570_, 18, v___x_543_);
lean_closure_set(v___f_570_, 19, v___x_558_);
v___x_571_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_566_, v___f_570_, v___x_555_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_545_, v___x_573_);
v___x_575_ = lean_array_uset(v_bs_x27_561_, v_i_545_, v_a_572_);
v_i_545_ = v___x_574_;
v_bs_546_ = v___x_575_;
goto _start;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v_bs_x27_561_);
lean_dec_ref(v___x_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_indName_540_);
lean_dec_ref(v_val_539_);
lean_dec_ref(v_motive_538_);
lean_dec_ref(v_ism2_537_);
lean_dec(v___x_536_);
lean_dec_ref(v_alts_535_);
lean_dec_ref(v_params_534_);
lean_dec(v_tail_533_);
v_a_577_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_571_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_571_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_564_);
lean_dec(v___x_562_);
lean_dec_ref(v_bs_x27_561_);
lean_dec(v_v_559_);
lean_dec_ref(v___x_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_indName_540_);
lean_dec_ref(v_val_539_);
lean_dec_ref(v_motive_538_);
lean_dec_ref(v_ism2_537_);
lean_dec(v___x_536_);
lean_dec_ref(v_alts_535_);
lean_dec_ref(v_params_534_);
lean_dec(v_tail_533_);
v_a_585_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_565_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_565_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_593_ = _args[0];
lean_object* v_params_594_ = _args[1];
lean_object* v_alts_595_ = _args[2];
lean_object* v___x_596_ = _args[3];
lean_object* v_ism2_597_ = _args[4];
lean_object* v_motive_598_ = _args[5];
lean_object* v_val_599_ = _args[6];
lean_object* v_indName_600_ = _args[7];
lean_object* v___x_601_ = _args[8];
lean_object* v___x_602_ = _args[9];
lean_object* v___x_603_ = _args[10];
lean_object* v_sz_604_ = _args[11];
lean_object* v_i_605_ = _args[12];
lean_object* v_bs_606_ = _args[13];
lean_object* v___y_607_ = _args[14];
lean_object* v___y_608_ = _args[15];
lean_object* v___y_609_ = _args[16];
lean_object* v___y_610_ = _args[17];
lean_object* v___y_611_ = _args[18];
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_604_);
lean_dec(v_sz_604_);
v_i_boxed_613_ = lean_unbox_usize(v_i_605_);
lean_dec(v_i_605_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_593_, v_params_594_, v_alts_595_, v___x_596_, v_ism2_597_, v_motive_598_, v_val_599_, v_indName_600_, v___x_601_, v___x_602_, v___x_603_, v_sz_boxed_612_, v_i_boxed_613_, v_bs_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_615_, lean_object* v___x_616_, lean_object* v_a_617_, lean_object* v_ism1_618_, uint8_t v___x_619_, uint8_t v___x_620_, uint8_t v___x_621_, lean_object* v_name_622_, lean_object* v___x_623_, lean_object* v_params_624_, lean_object* v___x_625_, lean_object* v_tail_626_, lean_object* v_alts_627_, lean_object* v_numParams_628_, lean_object* v_ism2_629_, lean_object* v_val_630_, lean_object* v_indName_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_heq_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_inc_ref(v_motive_615_);
v___x_641_ = l_Lean_mkAppN(v_motive_615_, v___x_616_);
v___x_642_ = l_Lean_mkArrow(v_a_617_, v___x_641_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = l_Lean_Meta_mkLambdaFVars(v_ism1_618_, v_a_643_, v___x_619_, v___x_620_, v___x_619_, v___x_620_, v___x_621_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
lean_inc(v___x_623_);
v___x_646_ = l_Lean_mkConst(v_name_622_, v___x_623_);
v___x_647_ = l_Lean_mkAppN(v___x_646_, v_params_624_);
v___x_648_ = l_Lean_Expr_app___override(v___x_647_, v_a_645_);
v___x_649_ = l_Lean_mkAppN(v___x_648_, v_ism1_618_);
v_sz_650_ = lean_array_size(v___x_625_);
v___x_651_ = ((size_t)0ULL);
lean_inc_ref(v_motive_615_);
lean_inc_ref(v_ism2_629_);
lean_inc_ref(v_alts_627_);
lean_inc_ref(v_params_624_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_626_, v_params_624_, v_alts_627_, v_numParams_628_, v_ism2_629_, v_motive_615_, v_val_630_, v_indName_631_, v___x_623_, v___x_632_, v___x_633_, v_sz_650_, v___x_651_, v___x_625_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_mkAppN(v___x_649_, v_a_653_);
lean_dec(v_a_653_);
lean_inc_ref(v_heq_635_);
v___x_655_ = l_Lean_Meta_mkEqSymm(v_heq_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_Expr_app___override(v___x_654_, v_a_656_);
v___x_658_ = lean_mk_empty_array_with_capacity(v___x_634_);
lean_inc_ref(v___x_658_);
v___x_659_ = lean_array_push(v___x_658_, v_motive_615_);
v___x_660_ = l_Array_append___redArg(v_params_624_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = l_Array_append___redArg(v___x_660_, v_ism1_618_);
v___x_662_ = l_Array_append___redArg(v___x_661_, v_ism2_629_);
lean_dec_ref(v_ism2_629_);
v___x_663_ = lean_array_push(v___x_658_, v_heq_635_);
v___x_664_ = l_Array_append___redArg(v___x_662_, v___x_663_);
lean_dec_ref(v___x_663_);
v___x_665_ = l_Array_append___redArg(v___x_664_, v_alts_627_);
lean_dec_ref(v_alts_627_);
v___x_666_ = l_Lean_Meta_mkLambdaFVars(v___x_665_, v___x_657_, v___x_619_, v___x_620_, v___x_619_, v___x_620_, v___x_621_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec_ref(v___x_665_);
return v___x_666_;
}
else
{
lean_dec_ref(v___x_654_);
lean_dec_ref(v_heq_635_);
lean_dec_ref(v_ism2_629_);
lean_dec_ref(v_alts_627_);
lean_dec_ref(v_params_624_);
lean_dec_ref(v_motive_615_);
return v___x_655_;
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_heq_635_);
lean_dec_ref(v_ism2_629_);
lean_dec_ref(v_alts_627_);
lean_dec_ref(v_params_624_);
lean_dec_ref(v_motive_615_);
v_a_667_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_652_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_652_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_dec_ref(v_heq_635_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_indName_631_);
lean_dec_ref(v_val_630_);
lean_dec_ref(v_ism2_629_);
lean_dec(v_numParams_628_);
lean_dec_ref(v_alts_627_);
lean_dec(v_tail_626_);
lean_dec_ref(v___x_625_);
lean_dec_ref(v_params_624_);
lean_dec(v___x_623_);
lean_dec(v_name_622_);
lean_dec_ref(v_motive_615_);
return v___x_644_;
}
}
else
{
lean_dec_ref(v_heq_635_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_indName_631_);
lean_dec_ref(v_val_630_);
lean_dec_ref(v_ism2_629_);
lean_dec(v_numParams_628_);
lean_dec_ref(v_alts_627_);
lean_dec(v_tail_626_);
lean_dec_ref(v___x_625_);
lean_dec_ref(v_params_624_);
lean_dec(v___x_623_);
lean_dec(v_name_622_);
lean_dec_ref(v_motive_615_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_675_ = _args[0];
lean_object* v___x_676_ = _args[1];
lean_object* v_a_677_ = _args[2];
lean_object* v_ism1_678_ = _args[3];
lean_object* v___x_679_ = _args[4];
lean_object* v___x_680_ = _args[5];
lean_object* v___x_681_ = _args[6];
lean_object* v_name_682_ = _args[7];
lean_object* v___x_683_ = _args[8];
lean_object* v_params_684_ = _args[9];
lean_object* v___x_685_ = _args[10];
lean_object* v_tail_686_ = _args[11];
lean_object* v_alts_687_ = _args[12];
lean_object* v_numParams_688_ = _args[13];
lean_object* v_ism2_689_ = _args[14];
lean_object* v_val_690_ = _args[15];
lean_object* v_indName_691_ = _args[16];
lean_object* v___x_692_ = _args[17];
lean_object* v___x_693_ = _args[18];
lean_object* v___x_694_ = _args[19];
lean_object* v_heq_695_ = _args[20];
lean_object* v___y_696_ = _args[21];
lean_object* v___y_697_ = _args[22];
lean_object* v___y_698_ = _args[23];
lean_object* v___y_699_ = _args[24];
lean_object* v___y_700_ = _args[25];
_start:
{
uint8_t v___x_21512__boxed_701_; uint8_t v___x_21513__boxed_702_; uint8_t v___x_21514__boxed_703_; lean_object* v_res_704_; 
v___x_21512__boxed_701_ = lean_unbox(v___x_679_);
v___x_21513__boxed_702_ = lean_unbox(v___x_680_);
v___x_21514__boxed_703_ = lean_unbox(v___x_681_);
v_res_704_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_675_, v___x_676_, v_a_677_, v_ism1_678_, v___x_21512__boxed_701_, v___x_21513__boxed_702_, v___x_21514__boxed_703_, v_name_682_, v___x_683_, v_params_684_, v___x_685_, v_tail_686_, v_alts_687_, v_numParams_688_, v_ism2_689_, v_val_690_, v_indName_691_, v___x_692_, v___x_693_, v___x_694_, v_heq_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___x_694_);
lean_dec_ref(v_ism1_678_);
lean_dec_ref(v___x_676_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_705_, lean_object* v_tail_706_, lean_object* v_params_707_, lean_object* v_ism1_708_, lean_object* v_ism2_709_, lean_object* v_motive_710_, lean_object* v___x_711_, uint8_t v___x_712_, uint8_t v___x_713_, uint8_t v___x_714_, lean_object* v_name_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v_numParams_718_, lean_object* v_val_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_alts_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_inc(v_indName_705_);
v___x_728_ = l_Lean_mkCtorIdxName(v_indName_705_);
lean_inc(v_tail_706_);
v___x_729_ = l_Lean_mkConst(v___x_728_, v_tail_706_);
lean_inc_ref_n(v_params_707_, 2);
v___x_730_ = l_Array_append___redArg(v_params_707_, v_ism1_708_);
lean_inc_ref(v___x_729_);
v___x_731_ = l_Lean_mkAppN(v___x_729_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = l_Array_append___redArg(v_params_707_, v_ism2_709_);
v___x_733_ = l_Lean_mkAppN(v___x_729_, v___x_732_);
lean_dec_ref(v___x_732_);
lean_inc_ref(v___x_733_);
lean_inc_ref(v___x_731_);
v___x_734_ = l_Lean_Meta_mkEq(v___x_731_, v___x_733_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
lean_inc_ref(v___x_733_);
v___x_736_ = l_Lean_Meta_mkEq(v___x_733_, v___x_731_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = lean_box(v___x_712_);
v___x_739_ = lean_box(v___x_713_);
v___x_740_ = lean_box(v___x_714_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_741_, 0, v_motive_710_);
lean_closure_set(v___f_741_, 1, v___x_711_);
lean_closure_set(v___f_741_, 2, v_a_737_);
lean_closure_set(v___f_741_, 3, v_ism1_708_);
lean_closure_set(v___f_741_, 4, v___x_738_);
lean_closure_set(v___f_741_, 5, v___x_739_);
lean_closure_set(v___f_741_, 6, v___x_740_);
lean_closure_set(v___f_741_, 7, v_name_715_);
lean_closure_set(v___f_741_, 8, v___x_716_);
lean_closure_set(v___f_741_, 9, v_params_707_);
lean_closure_set(v___f_741_, 10, v___x_717_);
lean_closure_set(v___f_741_, 11, v_tail_706_);
lean_closure_set(v___f_741_, 12, v_alts_722_);
lean_closure_set(v___f_741_, 13, v_numParams_718_);
lean_closure_set(v___f_741_, 14, v_ism2_709_);
lean_closure_set(v___f_741_, 15, v_val_719_);
lean_closure_set(v___f_741_, 16, v_indName_705_);
lean_closure_set(v___f_741_, 17, v___x_720_);
lean_closure_set(v___f_741_, 18, v___x_733_);
lean_closure_set(v___f_741_, 19, v___x_721_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_743_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_742_, v_a_735_, v___f_741_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
return v___x_743_;
}
else
{
lean_dec(v_a_735_);
lean_dec_ref(v___x_733_);
lean_dec_ref(v_alts_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec_ref(v_val_719_);
lean_dec(v_numParams_718_);
lean_dec_ref(v___x_717_);
lean_dec(v___x_716_);
lean_dec(v_name_715_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v_motive_710_);
lean_dec_ref(v_ism2_709_);
lean_dec_ref(v_ism1_708_);
lean_dec_ref(v_params_707_);
lean_dec(v_tail_706_);
lean_dec(v_indName_705_);
return v___x_736_;
}
}
else
{
lean_dec_ref(v___x_733_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v_alts_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec_ref(v_val_719_);
lean_dec(v_numParams_718_);
lean_dec_ref(v___x_717_);
lean_dec(v___x_716_);
lean_dec(v_name_715_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v_motive_710_);
lean_dec_ref(v_ism2_709_);
lean_dec_ref(v_ism1_708_);
lean_dec_ref(v_params_707_);
lean_dec(v_tail_706_);
lean_dec(v_indName_705_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_744_ = _args[0];
lean_object* v_tail_745_ = _args[1];
lean_object* v_params_746_ = _args[2];
lean_object* v_ism1_747_ = _args[3];
lean_object* v_ism2_748_ = _args[4];
lean_object* v_motive_749_ = _args[5];
lean_object* v___x_750_ = _args[6];
lean_object* v___x_751_ = _args[7];
lean_object* v___x_752_ = _args[8];
lean_object* v___x_753_ = _args[9];
lean_object* v_name_754_ = _args[10];
lean_object* v___x_755_ = _args[11];
lean_object* v___x_756_ = _args[12];
lean_object* v_numParams_757_ = _args[13];
lean_object* v_val_758_ = _args[14];
lean_object* v___x_759_ = _args[15];
lean_object* v___x_760_ = _args[16];
lean_object* v_alts_761_ = _args[17];
lean_object* v___y_762_ = _args[18];
lean_object* v___y_763_ = _args[19];
lean_object* v___y_764_ = _args[20];
lean_object* v___y_765_ = _args[21];
lean_object* v___y_766_ = _args[22];
_start:
{
uint8_t v___x_21635__boxed_767_; uint8_t v___x_21636__boxed_768_; uint8_t v___x_21637__boxed_769_; lean_object* v_res_770_; 
v___x_21635__boxed_767_ = lean_unbox(v___x_751_);
v___x_21636__boxed_768_ = lean_unbox(v___x_752_);
v___x_21637__boxed_769_ = lean_unbox(v___x_753_);
v_res_770_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_744_, v_tail_745_, v_params_746_, v_ism1_747_, v_ism2_748_, v_motive_749_, v___x_750_, v___x_21635__boxed_767_, v___x_21636__boxed_768_, v___x_21637__boxed_769_, v_name_754_, v___x_755_, v___x_756_, v_numParams_757_, v_val_758_, v___x_759_, v___x_760_, v_alts_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_771_, lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_snd_771_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_779_, v_x_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_x_780_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_787_, size_t v_i_788_, lean_object* v_bs_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = lean_usize_dec_lt(v_i_788_, v_sz_787_);
if (v___x_790_ == 0)
{
return v_bs_789_;
}
else
{
lean_object* v_v_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
v_v_791_ = lean_array_uget(v_bs_789_, v_i_788_);
v_fst_792_ = lean_ctor_get(v_v_791_, 0);
v_snd_793_ = lean_ctor_get(v_v_791_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_v_791_);
if (v_isSharedCheck_807_ == 0)
{
v___x_795_ = v_v_791_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_v_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_bs_x27_798_; lean_object* v___f_799_; lean_object* v___x_801_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v_bs_x27_798_ = lean_array_uset(v_bs_789_, v_i_788_, v___x_797_);
v___f_799_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_799_, 0, v_snd_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___f_799_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_fst_792_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___f_799_);
v___x_801_ = v_reuseFailAlloc_806_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_788_, v___x_802_);
v___x_804_ = lean_array_uset(v_bs_x27_798_, v_i_788_, v___x_801_);
v_i_788_ = v___x_803_;
v_bs_789_ = v___x_804_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_808_, lean_object* v_i_809_, lean_object* v_bs_810_){
_start:
{
size_t v_sz_boxed_811_; size_t v_i_boxed_812_; lean_object* v_res_813_; 
v_sz_boxed_811_ = lean_unbox_usize(v_sz_808_);
lean_dec(v_sz_808_);
v_i_boxed_812_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_811_, v_i_boxed_812_, v_bs_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0(lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v_a_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_20754__overap_822_; lean_object* v___x_823_; 
v___x_20754__overap_822_ = l_instInhabitedOfMonad___redArg(v___x_814_, v___x_815_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
v___x_823_ = lean_apply_5(v___x_20754__overap_822_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, lean_box(0));
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed(lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v_a_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0(v___x_824_, v___x_825_, v_a_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v_a_826_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0(void){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_instMonadEIO___redArg();
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0);
v___x_835_ = l_StateRefT_x27_instMonad___redArg(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1___boxed(lean_object* v_acc_840_, lean_object* v_declInfos_841_, lean_object* v_k_842_, lean_object* v_kind_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v_kind_boxed_850_; lean_object* v_res_851_; 
v_kind_boxed_850_ = lean_unbox(v_kind_843_);
v_res_851_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1(v_acc_840_, v_declInfos_841_, v_k_842_, v_kind_boxed_850_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(lean_object* v_declInfos_852_, lean_object* v_k_853_, uint8_t v_kind_854_, lean_object* v_acc_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_toApplicative_862_; lean_object* v_toFunctor_863_; lean_object* v_toSeq_864_; lean_object* v_toSeqLeft_865_; lean_object* v_toSeqRight_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_toApplicative_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_928_; 
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1);
v_toApplicative_862_ = lean_ctor_get(v___x_861_, 0);
v_toFunctor_863_ = lean_ctor_get(v_toApplicative_862_, 0);
v_toSeq_864_ = lean_ctor_get(v_toApplicative_862_, 2);
v_toSeqLeft_865_ = lean_ctor_get(v_toApplicative_862_, 3);
v_toSeqRight_866_ = lean_ctor_get(v_toApplicative_862_, 4);
v___f_867_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2));
v___f_868_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3));
lean_inc_ref_n(v_toFunctor_863_, 2);
v___f_869_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_869_, 0, v_toFunctor_863_);
v___f_870_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_870_, 0, v_toFunctor_863_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___f_869_);
lean_ctor_set(v___x_871_, 1, v___f_870_);
lean_inc(v_toSeqRight_866_);
v___f_872_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_872_, 0, v_toSeqRight_866_);
lean_inc(v_toSeqLeft_865_);
v___f_873_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_873_, 0, v_toSeqLeft_865_);
lean_inc(v_toSeq_864_);
v___f_874_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_874_, 0, v_toSeq_864_);
v___x_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_875_, 0, v___x_871_);
lean_ctor_set(v___x_875_, 1, v___f_867_);
lean_ctor_set(v___x_875_, 2, v___f_874_);
lean_ctor_set(v___x_875_, 3, v___f_873_);
lean_ctor_set(v___x_875_, 4, v___f_872_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___f_868_);
v___x_877_ = l_StateRefT_x27_instMonad___redArg(v___x_876_);
v_toApplicative_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v___x_877_, 1);
lean_dec(v_unused_929_);
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_928_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_toApplicative_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_928_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_toFunctor_882_; lean_object* v_toSeq_883_; lean_object* v_toSeqLeft_884_; lean_object* v_toSeqRight_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_926_; 
v_toFunctor_882_ = lean_ctor_get(v_toApplicative_878_, 0);
v_toSeq_883_ = lean_ctor_get(v_toApplicative_878_, 2);
v_toSeqLeft_884_ = lean_ctor_get(v_toApplicative_878_, 3);
v_toSeqRight_885_ = lean_ctor_get(v_toApplicative_878_, 4);
v_isSharedCheck_926_ = !lean_is_exclusive(v_toApplicative_878_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_toApplicative_878_, 1);
lean_dec(v_unused_927_);
v___x_887_ = v_toApplicative_878_;
v_isShared_888_ = v_isSharedCheck_926_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_toSeqRight_885_);
lean_inc(v_toSeqLeft_884_);
lean_inc(v_toSeq_883_);
lean_inc(v_toFunctor_882_);
lean_dec(v_toApplicative_878_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_926_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_898_; 
v___f_889_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4));
v___f_890_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5));
lean_inc_ref(v_toFunctor_882_);
v___f_891_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_891_, 0, v_toFunctor_882_);
v___f_892_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_892_, 0, v_toFunctor_882_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___f_891_);
lean_ctor_set(v___x_893_, 1, v___f_892_);
v___f_894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_894_, 0, v_toSeqRight_885_);
v___f_895_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_895_, 0, v_toSeqLeft_884_);
v___f_896_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_896_, 0, v_toSeq_883_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___f_894_);
lean_ctor_set(v___x_887_, 3, v___f_895_);
lean_ctor_set(v___x_887_, 2, v___f_896_);
lean_ctor_set(v___x_887_, 1, v___f_889_);
lean_ctor_set(v___x_887_, 0, v___x_893_);
v___x_898_ = v___x_887_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___f_889_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___f_896_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v___f_895_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v___f_894_);
v___x_898_ = v_reuseFailAlloc_925_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___f_890_);
lean_ctor_set(v___x_880_, 0, v___x_898_);
v___x_900_ = v___x_880_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___f_890_);
v___x_900_ = v_reuseFailAlloc_924_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_array_get_size(v_acc_855_);
v___x_902_ = lean_array_get_size(v_declInfos_852_);
v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_declInfos_852_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
v___x_904_ = lean_apply_6(v_k_853_, v_acc_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, lean_box(0));
return v___x_904_;
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_snd_914_; lean_object* v_fst_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
v___x_905_ = lean_box(0);
v___x_906_ = 0;
v___x_907_ = l_Lean_instInhabitedExpr;
v___f_908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed), 8, 2);
lean_closure_set(v___f_908_, 0, v___x_900_);
lean_closure_set(v___f_908_, 1, v___x_907_);
v___f_909_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_909_, 0, v___f_908_);
v___x_910_ = lean_box(v___x_906_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___f_909_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_905_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_array_get(v___x_912_, v_declInfos_852_, v___x_901_);
lean_dec_ref_known(v___x_912_, 2);
v_snd_914_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_snd_914_);
v_fst_915_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_915_);
lean_dec(v___x_913_);
v_fst_916_ = lean_ctor_get(v_snd_914_, 0);
lean_inc(v_fst_916_);
v_snd_917_ = lean_ctor_get(v_snd_914_, 1);
lean_inc(v_snd_917_);
lean_dec(v_snd_914_);
v___x_918_ = lean_box(v_kind_854_);
lean_inc_ref(v_acc_855_);
v___f_919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1___boxed), 10, 4);
lean_closure_set(v___f_919_, 0, v_acc_855_);
lean_closure_set(v___f_919_, 1, v_declInfos_852_);
lean_closure_set(v___f_919_, 2, v_k_853_);
lean_closure_set(v___f_919_, 3, v___x_918_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
v___x_920_ = lean_apply_6(v_snd_917_, v_acc_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, lean_box(0));
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; uint8_t v___x_922_; lean_object* v___x_923_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_unbox(v_fst_916_);
lean_dec(v_fst_916_);
v___x_923_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_915_, v___x_922_, v_a_921_, v___f_919_, v_kind_854_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_923_;
}
else
{
lean_dec_ref(v___f_919_);
lean_dec(v_fst_916_);
lean_dec(v_fst_915_);
return v___x_920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1(lean_object* v_acc_930_, lean_object* v_declInfos_931_, lean_object* v_k_932_, uint8_t v_kind_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_array_push(v_acc_930_, v_x_934_);
v___x_941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(v_declInfos_931_, v_k_932_, v_kind_933_, v___x_940_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___boxed(lean_object* v_declInfos_942_, lean_object* v_k_943_, lean_object* v_kind_944_, lean_object* v_acc_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v_kind_boxed_951_; lean_object* v_res_952_; 
v_kind_boxed_951_ = lean_unbox(v_kind_944_);
v_res_952_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(v_declInfos_942_, v_k_943_, v_kind_boxed_951_, v_acc_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(lean_object* v_declInfos_955_, lean_object* v_k_956_, uint8_t v_kind_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0));
v___x_964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(v_declInfos_955_, v_k_956_, v_kind_957_, v___x_963_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_declInfos_965_, lean_object* v_k_966_, lean_object* v_kind_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_kind_boxed_973_; lean_object* v_res_974_; 
v_kind_boxed_973_ = lean_unbox(v_kind_967_);
v_res_974_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_declInfos_965_, v_k_966_, v_kind_boxed_973_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(size_t v_sz_975_, size_t v_i_976_, lean_object* v_bs_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_978_ == 0)
{
return v_bs_977_;
}
else
{
lean_object* v_v_979_; lean_object* v_fst_980_; lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_997_; 
v_v_979_ = lean_array_uget(v_bs_977_, v_i_976_);
v_fst_980_ = lean_ctor_get(v_v_979_, 0);
v_snd_981_ = lean_ctor_get(v_v_979_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_v_979_);
if (v_isSharedCheck_997_ == 0)
{
v___x_983_ = v_v_979_;
v_isShared_984_ = v_isSharedCheck_997_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_inc(v_fst_980_);
lean_dec(v_v_979_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_997_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v_bs_x27_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_985_ = lean_unsigned_to_nat(0u);
v_bs_x27_986_ = lean_array_uset(v_bs_977_, v_i_976_, v___x_985_);
v___x_987_ = 0;
v___x_988_ = lean_box(v___x_987_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_988_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_snd_981_);
v___x_990_ = v_reuseFailAlloc_996_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_fst_980_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_976_, v___x_992_);
v___x_994_ = lean_array_uset(v_bs_x27_986_, v_i_976_, v___x_991_);
v_i_976_ = v___x_993_;
v_bs_977_ = v___x_994_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15___boxed(lean_object* v_sz_998_, lean_object* v_i_999_, lean_object* v_bs_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_998_);
lean_dec(v_sz_998_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_boxed_1001_, v_i_boxed_1002_, v_bs_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1004_, lean_object* v_k_1005_, uint8_t v_kind_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_sz_1012_; size_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_sz_1012_ = lean_array_size(v_declInfos_1004_);
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_1012_, v___x_1013_, v_declInfos_1004_);
v___x_1015_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v___x_1014_, v_k_1005_, v_kind_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1016_, lean_object* v_k_1017_, lean_object* v_kind_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v_kind_boxed_1024_; lean_object* v_res_1025_; 
v_kind_boxed_1024_ = lean_unbox(v_kind_1018_);
v_res_1025_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1016_, v_k_1017_, v_kind_boxed_1024_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1026_, lean_object* v_k_1027_, uint8_t v_kind_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_sz_1034_ = lean_array_size(v_declInfos_1026_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1034_, v___x_1035_, v_declInfos_1026_);
v___x_1037_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1036_, v_k_1027_, v_kind_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1038_, lean_object* v_k_1039_, lean_object* v_kind_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v_kind_boxed_1046_; lean_object* v_res_1047_; 
v_kind_boxed_1046_ = lean_unbox(v_kind_1040_);
v_res_1047_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1038_, v_k_1039_, v_kind_boxed_1046_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1049_, lean_object* v_dummy_1050_, lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v_motive_1054_, lean_object* v_zs1_1055_, uint8_t v___x_1056_, uint8_t v___x_1057_, uint8_t v___x_1058_, lean_object* v_v_1059_, lean_object* v___x_1060_, lean_object* v_zs2_1061_, lean_object* v_ctorRet2_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Lean_mkAppN(v___x_1049_, v_zs2_1061_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
v___x_1069_ = lean_whnf(v_ctorRet2_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_nargs_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v_nargs_1071_ = l_Lean_Expr_getAppNumArgs(v_a_1070_);
lean_inc(v_nargs_1071_);
v___x_1072_ = lean_mk_array(v_nargs_1071_, v_dummy_1050_);
v___x_1073_ = lean_nat_sub(v_nargs_1071_, v___x_1051_);
lean_dec(v_nargs_1071_);
v___x_1074_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1070_, v___x_1072_, v___x_1073_);
v___x_1075_ = lean_array_get_size(v___x_1074_);
v___x_1076_ = l_Array_toSubarray___redArg(v___x_1074_, v___x_1052_, v___x_1075_);
v___x_1077_ = l_Subarray_copy___redArg(v___x_1076_);
v___x_1078_ = lean_array_push(v___x_1077_, v___x_1068_);
v___x_1079_ = l_Array_append___redArg(v___x_1053_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = l_Lean_mkAppN(v_motive_1054_, v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l_Array_append___redArg(v_zs1_1055_, v_zs2_1061_);
v___x_1082_ = l_Lean_Meta_mkForallFVars(v___x_1081_, v___x_1080_, v___x_1056_, v___x_1057_, v___x_1057_, v___x_1058_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1102_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___y_1088_; 
if (lean_obj_tag(v_v_1059_) == 1)
{
lean_object* v_str_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_str_1093_ = lean_ctor_get(v_v_1059_, 1);
lean_inc_ref(v_str_1093_);
lean_dec_ref_known(v_v_1059_, 2);
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_Name_str___override(v___x_1094_, v_str_1093_);
v___y_1088_ = v___x_1095_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_v_1059_);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1097_ = lean_nat_add(v___x_1060_, v___x_1051_);
v___x_1098_ = l_Nat_reprFast(v___x_1097_);
v___x_1099_ = lean_string_append(v___x_1096_, v___x_1098_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_Name_str___override(v___x_1100_, v___x_1099_);
v___y_1088_ = v___x_1101_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1091_ = v___x_1085_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_v_1059_);
v_a_1103_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1082_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1082_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v___x_1068_);
lean_dec(v_v_1059_);
lean_dec_ref(v_zs1_1055_);
lean_dec_ref(v_motive_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
lean_dec_ref(v_dummy_1050_);
v_a_1111_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1069_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1069_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1119_ = _args[0];
lean_object* v_dummy_1120_ = _args[1];
lean_object* v___x_1121_ = _args[2];
lean_object* v___x_1122_ = _args[3];
lean_object* v___x_1123_ = _args[4];
lean_object* v_motive_1124_ = _args[5];
lean_object* v_zs1_1125_ = _args[6];
lean_object* v___x_1126_ = _args[7];
lean_object* v___x_1127_ = _args[8];
lean_object* v___x_1128_ = _args[9];
lean_object* v_v_1129_ = _args[10];
lean_object* v___x_1130_ = _args[11];
lean_object* v_zs2_1131_ = _args[12];
lean_object* v_ctorRet2_1132_ = _args[13];
lean_object* v___y_1133_ = _args[14];
lean_object* v___y_1134_ = _args[15];
lean_object* v___y_1135_ = _args[16];
lean_object* v___y_1136_ = _args[17];
lean_object* v___y_1137_ = _args[18];
_start:
{
uint8_t v___x_22074__boxed_1138_; uint8_t v___x_22075__boxed_1139_; uint8_t v___x_22076__boxed_1140_; lean_object* v_res_1141_; 
v___x_22074__boxed_1138_ = lean_unbox(v___x_1126_);
v___x_22075__boxed_1139_ = lean_unbox(v___x_1127_);
v___x_22076__boxed_1140_ = lean_unbox(v___x_1128_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1119_, v_dummy_1120_, v___x_1121_, v___x_1122_, v___x_1123_, v_motive_1124_, v_zs1_1125_, v___x_22074__boxed_1138_, v___x_22075__boxed_1139_, v___x_22076__boxed_1140_, v_v_1129_, v___x_1130_, v_zs2_1131_, v_ctorRet2_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec_ref(v_zs2_1131_);
lean_dec(v___x_1130_);
lean_dec(v___x_1121_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v_motive_1145_, uint8_t v___x_1146_, uint8_t v___x_1147_, uint8_t v___x_1148_, lean_object* v_v_1149_, lean_object* v___x_1150_, lean_object* v_a_1151_, lean_object* v_zs1_1152_, lean_object* v_ctorRet1_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v___x_1142_);
v___x_1159_ = l_Lean_mkAppN(v___x_1142_, v_zs1_1152_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
v___x_1160_ = lean_whnf(v_ctorRet1_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_dummy_1162_; lean_object* v_nargs_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v_dummy_1162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1163_ = l_Lean_Expr_getAppNumArgs(v_a_1161_);
lean_inc(v_nargs_1163_);
v___x_1164_ = lean_mk_array(v_nargs_1163_, v_dummy_1162_);
v___x_1165_ = lean_nat_sub(v_nargs_1163_, v___x_1143_);
lean_dec(v_nargs_1163_);
v___x_1166_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1161_, v___x_1164_, v___x_1165_);
v___x_1167_ = lean_array_get_size(v___x_1166_);
lean_inc(v___x_1144_);
v___x_1168_ = l_Array_toSubarray___redArg(v___x_1166_, v___x_1144_, v___x_1167_);
v___x_1169_ = l_Subarray_copy___redArg(v___x_1168_);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1159_);
v___x_1171_ = lean_box(v___x_1146_);
v___x_1172_ = lean_box(v___x_1147_);
v___x_1173_ = lean_box(v___x_1148_);
v___f_1174_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1174_, 0, v___x_1142_);
lean_closure_set(v___f_1174_, 1, v_dummy_1162_);
lean_closure_set(v___f_1174_, 2, v___x_1143_);
lean_closure_set(v___f_1174_, 3, v___x_1144_);
lean_closure_set(v___f_1174_, 4, v___x_1170_);
lean_closure_set(v___f_1174_, 5, v_motive_1145_);
lean_closure_set(v___f_1174_, 6, v_zs1_1152_);
lean_closure_set(v___f_1174_, 7, v___x_1171_);
lean_closure_set(v___f_1174_, 8, v___x_1172_);
lean_closure_set(v___f_1174_, 9, v___x_1173_);
lean_closure_set(v___f_1174_, 10, v_v_1149_);
lean_closure_set(v___f_1174_, 11, v___x_1150_);
v___x_1175_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1151_, v___f_1174_, v___x_1146_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1175_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v___x_1159_);
lean_dec_ref(v_zs1_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v___x_1150_);
lean_dec(v_v_1149_);
lean_dec_ref(v_motive_1145_);
lean_dec(v___x_1144_);
lean_dec(v___x_1143_);
lean_dec_ref(v___x_1142_);
v_a_1176_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1160_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1160_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1184_ = _args[0];
lean_object* v___x_1185_ = _args[1];
lean_object* v___x_1186_ = _args[2];
lean_object* v_motive_1187_ = _args[3];
lean_object* v___x_1188_ = _args[4];
lean_object* v___x_1189_ = _args[5];
lean_object* v___x_1190_ = _args[6];
lean_object* v_v_1191_ = _args[7];
lean_object* v___x_1192_ = _args[8];
lean_object* v_a_1193_ = _args[9];
lean_object* v_zs1_1194_ = _args[10];
lean_object* v_ctorRet1_1195_ = _args[11];
lean_object* v___y_1196_ = _args[12];
lean_object* v___y_1197_ = _args[13];
lean_object* v___y_1198_ = _args[14];
lean_object* v___y_1199_ = _args[15];
lean_object* v___y_1200_ = _args[16];
_start:
{
uint8_t v___x_22215__boxed_1201_; uint8_t v___x_22216__boxed_1202_; uint8_t v___x_22217__boxed_1203_; lean_object* v_res_1204_; 
v___x_22215__boxed_1201_ = lean_unbox(v___x_1188_);
v___x_22216__boxed_1202_ = lean_unbox(v___x_1189_);
v___x_22217__boxed_1203_ = lean_unbox(v___x_1190_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1184_, v___x_1185_, v___x_1186_, v_motive_1187_, v___x_22215__boxed_1201_, v___x_22216__boxed_1202_, v___x_22217__boxed_1203_, v_v_1191_, v___x_1192_, v_a_1193_, v_zs1_1194_, v_ctorRet1_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1205_, lean_object* v_params_1206_, lean_object* v___x_1207_, lean_object* v_motive_1208_, size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_bs_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec_ref(v_motive_1208_);
lean_dec(v___x_1207_);
lean_dec(v_tail_1205_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_bs_1211_);
return v___x_1218_;
}
else
{
uint8_t v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_bs_x27_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1219_ = 0;
v___x_1220_ = 1;
v___x_1221_ = lean_unsigned_to_nat(1u);
v_v_1222_ = lean_array_uget(v_bs_1211_, v_i_1210_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v_bs_x27_1224_ = lean_array_uset(v_bs_1211_, v_i_1210_, v___x_1223_);
v___x_1225_ = lean_usize_to_nat(v_i_1210_);
lean_inc(v_tail_1205_);
lean_inc(v_v_1222_);
v___x_1226_ = l_Lean_mkConst(v_v_1222_, v_tail_1205_);
v___x_1227_ = l_Lean_mkAppN(v___x_1226_, v_params_1206_);
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc_ref(v___x_1227_);
v___x_1228_ = lean_infer_type(v___x_1227_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_n(v_a_1229_, 2);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = lean_box(v___x_1219_);
v___x_1231_ = lean_box(v___x_1217_);
v___x_1232_ = lean_box(v___x_1220_);
lean_inc_ref(v_motive_1208_);
lean_inc(v___x_1207_);
v___f_1233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1233_, 0, v___x_1227_);
lean_closure_set(v___f_1233_, 1, v___x_1221_);
lean_closure_set(v___f_1233_, 2, v___x_1207_);
lean_closure_set(v___f_1233_, 3, v_motive_1208_);
lean_closure_set(v___f_1233_, 4, v___x_1230_);
lean_closure_set(v___f_1233_, 5, v___x_1231_);
lean_closure_set(v___f_1233_, 6, v___x_1232_);
lean_closure_set(v___f_1233_, 7, v_v_1222_);
lean_closure_set(v___f_1233_, 8, v___x_1225_);
lean_closure_set(v___f_1233_, 9, v_a_1229_);
v___x_1234_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1229_, v___f_1233_, v___x_1219_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = ((size_t)1ULL);
v___x_1237_ = lean_usize_add(v_i_1210_, v___x_1236_);
v___x_1238_ = lean_array_uset(v_bs_x27_1224_, v_i_1210_, v_a_1235_);
v_i_1210_ = v___x_1237_;
v_bs_1211_ = v___x_1238_;
goto _start;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_bs_x27_1224_);
lean_dec_ref(v_motive_1208_);
lean_dec(v___x_1207_);
lean_dec(v_tail_1205_);
v_a_1240_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1234_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1234_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
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
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v___x_1227_);
lean_dec(v___x_1225_);
lean_dec_ref(v_bs_x27_1224_);
lean_dec(v_v_1222_);
lean_dec_ref(v_motive_1208_);
lean_dec(v___x_1207_);
lean_dec(v_tail_1205_);
v_a_1248_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1228_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1228_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1256_, lean_object* v_params_1257_, lean_object* v___x_1258_, lean_object* v_motive_1259_, lean_object* v_sz_1260_, lean_object* v_i_1261_, lean_object* v_bs_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
size_t v_sz_boxed_1268_; size_t v_i_boxed_1269_; lean_object* v_res_1270_; 
v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1256_, v_params_1257_, v___x_1258_, v_motive_1259_, v_sz_boxed_1268_, v_i_boxed_1269_, v_bs_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_params_1257_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1271_, lean_object* v_indName_1272_, lean_object* v_tail_1273_, lean_object* v_params_1274_, lean_object* v_ism1_1275_, lean_object* v_ism2_1276_, lean_object* v___x_1277_, uint8_t v___x_1278_, uint8_t v___x_1279_, uint8_t v___x_1280_, lean_object* v_name_1281_, lean_object* v___x_1282_, lean_object* v_numParams_1283_, lean_object* v_val_1284_, lean_object* v___x_1285_, lean_object* v___x_1286_, lean_object* v_motive_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; size_t v_sz_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1293_ = lean_array_mk(v_ctors_1271_);
v___x_1294_ = lean_box(v___x_1278_);
v___x_1295_ = lean_box(v___x_1279_);
v___x_1296_ = lean_box(v___x_1280_);
lean_inc(v_numParams_1283_);
lean_inc_ref(v___x_1293_);
lean_inc_ref(v_motive_1287_);
lean_inc_ref(v_params_1274_);
lean_inc(v_tail_1273_);
v___f_1297_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1297_, 0, v_indName_1272_);
lean_closure_set(v___f_1297_, 1, v_tail_1273_);
lean_closure_set(v___f_1297_, 2, v_params_1274_);
lean_closure_set(v___f_1297_, 3, v_ism1_1275_);
lean_closure_set(v___f_1297_, 4, v_ism2_1276_);
lean_closure_set(v___f_1297_, 5, v_motive_1287_);
lean_closure_set(v___f_1297_, 6, v___x_1277_);
lean_closure_set(v___f_1297_, 7, v___x_1294_);
lean_closure_set(v___f_1297_, 8, v___x_1295_);
lean_closure_set(v___f_1297_, 9, v___x_1296_);
lean_closure_set(v___f_1297_, 10, v_name_1281_);
lean_closure_set(v___f_1297_, 11, v___x_1282_);
lean_closure_set(v___f_1297_, 12, v___x_1293_);
lean_closure_set(v___f_1297_, 13, v_numParams_1283_);
lean_closure_set(v___f_1297_, 14, v_val_1284_);
lean_closure_set(v___f_1297_, 15, v___x_1285_);
lean_closure_set(v___f_1297_, 16, v___x_1286_);
v_sz_1298_ = lean_array_size(v___x_1293_);
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1273_, v_params_1274_, v_numParams_1283_, v_motive_1287_, v_sz_1298_, v___x_1299_, v___x_1293_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec_ref(v_params_1274_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = 0;
v___x_1303_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1301_, v___f_1297_, v___x_1302_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1303_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___f_1297_);
v_a_1304_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1300_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1300_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1312_ = _args[0];
lean_object* v_indName_1313_ = _args[1];
lean_object* v_tail_1314_ = _args[2];
lean_object* v_params_1315_ = _args[3];
lean_object* v_ism1_1316_ = _args[4];
lean_object* v_ism2_1317_ = _args[5];
lean_object* v___x_1318_ = _args[6];
lean_object* v___x_1319_ = _args[7];
lean_object* v___x_1320_ = _args[8];
lean_object* v___x_1321_ = _args[9];
lean_object* v_name_1322_ = _args[10];
lean_object* v___x_1323_ = _args[11];
lean_object* v_numParams_1324_ = _args[12];
lean_object* v_val_1325_ = _args[13];
lean_object* v___x_1326_ = _args[14];
lean_object* v___x_1327_ = _args[15];
lean_object* v_motive_1328_ = _args[16];
lean_object* v___y_1329_ = _args[17];
lean_object* v___y_1330_ = _args[18];
lean_object* v___y_1331_ = _args[19];
lean_object* v___y_1332_ = _args[20];
lean_object* v___y_1333_ = _args[21];
_start:
{
uint8_t v___x_22395__boxed_1334_; uint8_t v___x_22396__boxed_1335_; uint8_t v___x_22397__boxed_1336_; lean_object* v_res_1337_; 
v___x_22395__boxed_1334_ = lean_unbox(v___x_1319_);
v___x_22396__boxed_1335_ = lean_unbox(v___x_1320_);
v___x_22397__boxed_1336_ = lean_unbox(v___x_1321_);
v_res_1337_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1312_, v_indName_1313_, v_tail_1314_, v_params_1315_, v_ism1_1316_, v_ism2_1317_, v___x_1318_, v___x_22395__boxed_1334_, v___x_22396__boxed_1335_, v___x_22397__boxed_1336_, v_name_1322_, v___x_1323_, v_numParams_1324_, v_val_1325_, v___x_1326_, v___x_1327_, v_motive_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1341_, lean_object* v_head_1342_, lean_object* v_ctors_1343_, lean_object* v_indName_1344_, lean_object* v_tail_1345_, lean_object* v_params_1346_, lean_object* v_name_1347_, lean_object* v___x_1348_, lean_object* v_numParams_1349_, lean_object* v_val_1350_, lean_object* v___x_1351_, lean_object* v___x_1352_, lean_object* v_ism2_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; uint8_t v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; 
lean_inc_ref(v_ism1_1341_);
v___x_1360_ = l_Array_append___redArg(v_ism1_1341_, v_ism2_1353_);
v___x_1361_ = l_Lean_mkSort(v_head_1342_);
v___x_1362_ = 0;
v___x_1363_ = 1;
v___x_1364_ = 1;
v___x_1365_ = lean_box(v___x_1362_);
v___x_1366_ = lean_box(v___x_1363_);
v___x_1367_ = lean_box(v___x_1364_);
lean_inc_ref(v___x_1360_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1368_, 0, v_ctors_1343_);
lean_closure_set(v___f_1368_, 1, v_indName_1344_);
lean_closure_set(v___f_1368_, 2, v_tail_1345_);
lean_closure_set(v___f_1368_, 3, v_params_1346_);
lean_closure_set(v___f_1368_, 4, v_ism1_1341_);
lean_closure_set(v___f_1368_, 5, v_ism2_1353_);
lean_closure_set(v___f_1368_, 6, v___x_1360_);
lean_closure_set(v___f_1368_, 7, v___x_1365_);
lean_closure_set(v___f_1368_, 8, v___x_1366_);
lean_closure_set(v___f_1368_, 9, v___x_1367_);
lean_closure_set(v___f_1368_, 10, v_name_1347_);
lean_closure_set(v___f_1368_, 11, v___x_1348_);
lean_closure_set(v___f_1368_, 12, v_numParams_1349_);
lean_closure_set(v___f_1368_, 13, v_val_1350_);
lean_closure_set(v___f_1368_, 14, v___x_1351_);
lean_closure_set(v___f_1368_, 15, v___x_1352_);
v___x_1369_ = l_Lean_Meta_mkForallFVars(v___x_1360_, v___x_1361_, v___x_1362_, v___x_1363_, v___x_1363_, v___x_1364_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v___x_1360_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1372_ = 0;
v___x_1373_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1371_, v___x_1364_, v_a_1370_, v___f_1368_, v___x_1372_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1373_;
}
else
{
lean_dec_ref(v___f_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1374_ = _args[0];
lean_object* v_head_1375_ = _args[1];
lean_object* v_ctors_1376_ = _args[2];
lean_object* v_indName_1377_ = _args[3];
lean_object* v_tail_1378_ = _args[4];
lean_object* v_params_1379_ = _args[5];
lean_object* v_name_1380_ = _args[6];
lean_object* v___x_1381_ = _args[7];
lean_object* v_numParams_1382_ = _args[8];
lean_object* v_val_1383_ = _args[9];
lean_object* v___x_1384_ = _args[10];
lean_object* v___x_1385_ = _args[11];
lean_object* v_ism2_1386_ = _args[12];
lean_object* v_x_1387_ = _args[13];
lean_object* v___y_1388_ = _args[14];
lean_object* v___y_1389_ = _args[15];
lean_object* v___y_1390_ = _args[16];
lean_object* v___y_1391_ = _args[17];
lean_object* v___y_1392_ = _args[18];
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1374_, v_head_1375_, v_ctors_1376_, v_indName_1377_, v_tail_1378_, v_params_1379_, v_name_1380_, v___x_1381_, v_numParams_1382_, v_val_1383_, v___x_1384_, v___x_1385_, v_ism2_1386_, v_x_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_x_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1394_, lean_object* v_ctors_1395_, lean_object* v_indName_1396_, lean_object* v_tail_1397_, lean_object* v_params_1398_, lean_object* v_name_1399_, lean_object* v___x_1400_, lean_object* v_numParams_1401_, lean_object* v_val_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v_t_1405_, lean_object* v___x_1406_, lean_object* v_ism1_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___f_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; 
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1414_, 0, v_ism1_1407_);
lean_closure_set(v___f_1414_, 1, v_head_1394_);
lean_closure_set(v___f_1414_, 2, v_ctors_1395_);
lean_closure_set(v___f_1414_, 3, v_indName_1396_);
lean_closure_set(v___f_1414_, 4, v_tail_1397_);
lean_closure_set(v___f_1414_, 5, v_params_1398_);
lean_closure_set(v___f_1414_, 6, v_name_1399_);
lean_closure_set(v___f_1414_, 7, v___x_1400_);
lean_closure_set(v___f_1414_, 8, v_numParams_1401_);
lean_closure_set(v___f_1414_, 9, v_val_1402_);
lean_closure_set(v___f_1414_, 10, v___x_1403_);
lean_closure_set(v___f_1414_, 11, v___x_1404_);
v___x_1415_ = 0;
v___x_1416_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1405_, v___x_1406_, v___f_1414_, v___x_1415_, v___x_1415_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1417_ = _args[0];
lean_object* v_ctors_1418_ = _args[1];
lean_object* v_indName_1419_ = _args[2];
lean_object* v_tail_1420_ = _args[3];
lean_object* v_params_1421_ = _args[4];
lean_object* v_name_1422_ = _args[5];
lean_object* v___x_1423_ = _args[6];
lean_object* v_numParams_1424_ = _args[7];
lean_object* v_val_1425_ = _args[8];
lean_object* v___x_1426_ = _args[9];
lean_object* v___x_1427_ = _args[10];
lean_object* v_t_1428_ = _args[11];
lean_object* v___x_1429_ = _args[12];
lean_object* v_ism1_1430_ = _args[13];
lean_object* v_x_1431_ = _args[14];
lean_object* v___y_1432_ = _args[15];
lean_object* v___y_1433_ = _args[16];
lean_object* v___y_1434_ = _args[17];
lean_object* v___y_1435_ = _args[18];
lean_object* v___y_1436_ = _args[19];
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1417_, v_ctors_1418_, v_indName_1419_, v_tail_1420_, v_params_1421_, v_name_1422_, v___x_1423_, v_numParams_1424_, v_val_1425_, v___x_1426_, v___x_1427_, v_t_1428_, v___x_1429_, v_ism1_1430_, v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_x_1431_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1438_, lean_object* v___x_1439_, lean_object* v_head_1440_, lean_object* v_ctors_1441_, lean_object* v_indName_1442_, lean_object* v_tail_1443_, lean_object* v_params_1444_, lean_object* v_name_1445_, lean_object* v___x_1446_, lean_object* v_numParams_1447_, lean_object* v_val_1448_, lean_object* v___x_1449_, lean_object* v_x_1450_, lean_object* v_t_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1457_ = lean_nat_add(v_numIndices_1438_, v___x_1439_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_inc_ref(v___x_1458_);
lean_inc_ref(v_t_1451_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1459_, 0, v_head_1440_);
lean_closure_set(v___f_1459_, 1, v_ctors_1441_);
lean_closure_set(v___f_1459_, 2, v_indName_1442_);
lean_closure_set(v___f_1459_, 3, v_tail_1443_);
lean_closure_set(v___f_1459_, 4, v_params_1444_);
lean_closure_set(v___f_1459_, 5, v_name_1445_);
lean_closure_set(v___f_1459_, 6, v___x_1446_);
lean_closure_set(v___f_1459_, 7, v_numParams_1447_);
lean_closure_set(v___f_1459_, 8, v_val_1448_);
lean_closure_set(v___f_1459_, 9, v___x_1449_);
lean_closure_set(v___f_1459_, 10, v___x_1439_);
lean_closure_set(v___f_1459_, 11, v_t_1451_);
lean_closure_set(v___f_1459_, 12, v___x_1458_);
v___x_1460_ = 0;
v___x_1461_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1451_, v___x_1458_, v___f_1459_, v___x_1460_, v___x_1460_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1462_ = _args[0];
lean_object* v___x_1463_ = _args[1];
lean_object* v_head_1464_ = _args[2];
lean_object* v_ctors_1465_ = _args[3];
lean_object* v_indName_1466_ = _args[4];
lean_object* v_tail_1467_ = _args[5];
lean_object* v_params_1468_ = _args[6];
lean_object* v_name_1469_ = _args[7];
lean_object* v___x_1470_ = _args[8];
lean_object* v_numParams_1471_ = _args[9];
lean_object* v_val_1472_ = _args[10];
lean_object* v___x_1473_ = _args[11];
lean_object* v_x_1474_ = _args[12];
lean_object* v_t_1475_ = _args[13];
lean_object* v___y_1476_ = _args[14];
lean_object* v___y_1477_ = _args[15];
lean_object* v___y_1478_ = _args[16];
lean_object* v___y_1479_ = _args[17];
lean_object* v___y_1480_ = _args[18];
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1462_, v___x_1463_, v_head_1464_, v_ctors_1465_, v_indName_1466_, v_tail_1467_, v_params_1468_, v_name_1469_, v___x_1470_, v_numParams_1471_, v_val_1472_, v___x_1473_, v_x_1474_, v_t_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v_x_1474_);
lean_dec(v_numIndices_1462_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1484_, lean_object* v_head_1485_, lean_object* v_ctors_1486_, lean_object* v_indName_1487_, lean_object* v_tail_1488_, lean_object* v_name_1489_, lean_object* v___x_1490_, lean_object* v_numParams_1491_, lean_object* v_val_1492_, lean_object* v___x_1493_, lean_object* v_params_1494_, lean_object* v_t_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = lean_unsigned_to_nat(1u);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1502_, 0, v_numIndices_1484_);
lean_closure_set(v___f_1502_, 1, v___x_1501_);
lean_closure_set(v___f_1502_, 2, v_head_1485_);
lean_closure_set(v___f_1502_, 3, v_ctors_1486_);
lean_closure_set(v___f_1502_, 4, v_indName_1487_);
lean_closure_set(v___f_1502_, 5, v_tail_1488_);
lean_closure_set(v___f_1502_, 6, v_params_1494_);
lean_closure_set(v___f_1502_, 7, v_name_1489_);
lean_closure_set(v___f_1502_, 8, v___x_1490_);
lean_closure_set(v___f_1502_, 9, v_numParams_1491_);
lean_closure_set(v___f_1502_, 10, v_val_1492_);
lean_closure_set(v___f_1502_, 11, v___x_1493_);
v___x_1503_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1504_ = 0;
v___x_1505_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1495_, v___x_1503_, v___f_1502_, v___x_1504_, v___x_1504_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1506_ = _args[0];
lean_object* v_head_1507_ = _args[1];
lean_object* v_ctors_1508_ = _args[2];
lean_object* v_indName_1509_ = _args[3];
lean_object* v_tail_1510_ = _args[4];
lean_object* v_name_1511_ = _args[5];
lean_object* v___x_1512_ = _args[6];
lean_object* v_numParams_1513_ = _args[7];
lean_object* v_val_1514_ = _args[8];
lean_object* v___x_1515_ = _args[9];
lean_object* v_params_1516_ = _args[10];
lean_object* v_t_1517_ = _args[11];
lean_object* v___y_1518_ = _args[12];
lean_object* v___y_1519_ = _args[13];
lean_object* v___y_1520_ = _args[14];
lean_object* v___y_1521_ = _args[15];
lean_object* v___y_1522_ = _args[16];
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1506_, v_head_1507_, v_ctors_1508_, v_indName_1509_, v_tail_1510_, v_name_1511_, v___x_1512_, v_numParams_1513_, v_val_1514_, v___x_1515_, v_params_1516_, v_t_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1524_, lean_object* v_declName_1525_, lean_object* v_levelParams_1526_, uint8_t v___x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc_ref(v_a_1524_);
v___x_1533_ = lean_infer_type(v_a_1524_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = lean_box(1);
v___x_1536_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1525_, v_levelParams_1526_, v_a_1534_, v_a_1524_, v___x_1535_, v___y_1531_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_addDecl(v___x_1542_, v___x_1527_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v_levelParams_1526_);
lean_dec(v_declName_1525_);
lean_dec_ref(v_a_1524_);
v_a_1546_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1533_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1533_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1554_, lean_object* v_declName_1555_, lean_object* v_levelParams_1556_, lean_object* v___x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v___x_22683__boxed_1563_; lean_object* v_res_1564_; 
v___x_22683__boxed_1563_ = lean_unbox(v___x_1557_);
v_res_1564_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1554_, v_declName_1555_, v_levelParams_1556_, v___x_22683__boxed_1563_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
if (lean_obj_tag(v_a_1565_) == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = l_List_reverse___redArg(v_a_1566_);
return v___x_1567_;
}
else
{
lean_object* v_head_1568_; lean_object* v_tail_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1578_; 
v_head_1568_ = lean_ctor_get(v_a_1565_, 0);
v_tail_1569_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1571_ = v_a_1565_;
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_tail_1569_);
lean_inc(v_head_1568_);
lean_dec(v_a_1565_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = l_Lean_mkLevelParam(v_head_1568_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v_a_1566_);
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_a_1566_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v_a_1565_ = v_tail_1569_;
v_a_1566_ = v___x_1575_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(lean_object* v_msgData_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v_env_1586_; uint8_t v___x_1587_; lean_object* v_env_1588_; lean_object* v___x_1589_; lean_object* v_toCold_1590_; lean_object* v_mctx_1591_; lean_object* v_lctx_1592_; lean_object* v_options_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1585_ = lean_st_ref_get(v___y_1583_);
v_env_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_env_1586_);
lean_dec(v___x_1585_);
v___x_1587_ = 0;
v_env_1588_ = l_Lean_Environment_setRecordingDeps(v_env_1586_, v___x_1587_);
v___x_1589_ = lean_st_ref_get(v___y_1581_);
v_toCold_1590_ = lean_ctor_get(v___y_1582_, 0);
v_mctx_1591_ = lean_ctor_get(v___x_1589_, 0);
lean_inc_ref(v_mctx_1591_);
lean_dec(v___x_1589_);
v_lctx_1592_ = lean_ctor_get(v___y_1580_, 2);
v_options_1593_ = lean_ctor_get(v_toCold_1590_, 2);
lean_inc_ref(v_options_1593_);
lean_inc_ref(v_lctx_1592_);
v___x_1594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1594_, 0, v_env_1588_);
lean_ctor_set(v___x_1594_, 1, v_mctx_1591_);
lean_ctor_set(v___x_1594_, 2, v_lctx_1592_);
lean_ctor_set(v___x_1594_, 3, v_options_1593_);
v___x_1595_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_msgData_1579_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26___boxed(lean_object* v_msgData_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(v_msgData_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_ref_1610_; lean_object* v___x_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_ref_1610_ = lean_ctor_get(v___y_1607_, 2);
v___x_1611_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(v_msg_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_inc(v_ref_1610_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_ref_1610_);
lean_ctor_set(v___x_1616_, 1, v_a_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg___boxed(lean_object* v_msg_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(lean_object* v_ref_1628_, lean_object* v_msg_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_toCold_1635_; lean_object* v_currRecDepth_1636_; lean_object* v_ref_1637_; uint16_t v_optionFlags_1638_; uint8_t v_suppressElabErrors_1639_; uint8_t v_checkDeprecated_1640_; uint8_t v_isRecordingDeps_1641_; lean_object* v_ref_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toCold_1635_ = lean_ctor_get(v___y_1632_, 0);
v_currRecDepth_1636_ = lean_ctor_get(v___y_1632_, 1);
v_ref_1637_ = lean_ctor_get(v___y_1632_, 2);
v_optionFlags_1638_ = lean_ctor_get_uint16(v___y_1632_, sizeof(void*)*3);
v_suppressElabErrors_1639_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 2);
v_checkDeprecated_1640_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1641_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 4);
v_ref_1642_ = l_Lean_replaceRef(v_ref_1628_, v_ref_1637_);
lean_inc(v_currRecDepth_1636_);
lean_inc_ref(v_toCold_1635_);
v___x_1643_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1643_, 0, v_toCold_1635_);
lean_ctor_set(v___x_1643_, 1, v_currRecDepth_1636_);
lean_ctor_set(v___x_1643_, 2, v_ref_1642_);
lean_ctor_set_uint16(v___x_1643_, sizeof(void*)*3, v_optionFlags_1638_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3 + 2, v_suppressElabErrors_1639_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3 + 3, v_checkDeprecated_1640_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3 + 4, v_isRecordingDeps_1641_);
v___x_1644_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_1629_, v___y_1630_, v___y_1631_, v___x_1643_, v___y_1633_);
lean_dec_ref_known(v___x_1643_, 3);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg___boxed(lean_object* v_ref_1645_, lean_object* v_msg_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_1645_, v_msg_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v_ref_1645_);
return v_res_1652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0(void){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
lean_ctor_set(v___x_1659_, 3, v___x_1658_);
lean_ctor_set(v___x_1659_, 4, v___x_1657_);
lean_ctor_set(v___x_1659_, 5, v___x_1657_);
lean_ctor_set(v___x_1659_, 6, v___x_1657_);
lean_ctor_set(v___x_1659_, 7, v___x_1657_);
lean_ctor_set(v___x_1659_, 8, v___x_1657_);
lean_ctor_set(v___x_1659_, 9, v___x_1657_);
lean_ctor_set(v___x_1659_, 10, v___x_1657_);
lean_ctor_set(v___x_1659_, 11, v___x_1656_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(32u);
v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1660_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4(void){
_start:
{
size_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1663_ = ((size_t)5ULL);
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_unsigned_to_nat(32u);
v___x_1666_ = lean_mk_empty_array_with_capacity(v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3);
v___x_1668_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1666_);
lean_ctor_set(v___x_1668_, 2, v___x_1664_);
lean_ctor_set(v___x_1668_, 3, v___x_1664_);
lean_ctor_set_usize(v___x_1668_, 4, v___x_1663_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = lean_box(1);
v___x_1670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4);
v___x_1671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1);
v___x_1672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
lean_ctor_set(v___x_1672_, 2, v___x_1669_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12));
v___x_1684_ = l_Lean_stringToMessageData(v___x_1683_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14));
v___x_1687_ = l_Lean_stringToMessageData(v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18));
v___x_1693_ = l_Lean_stringToMessageData(v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(lean_object* v_msg_1694_, lean_object* v_declHint_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_env_1700_; uint8_t v___x_1701_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_st_ref_get(v___y_1696_);
v_env_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc_ref(v_env_1700_);
lean_dec(v___x_1699_);
v___x_1701_ = l_Lean_Name_isAnonymous(v_declHint_1695_);
if (v___x_1701_ == 0)
{
uint8_t v_isExporting_1702_; 
v_isExporting_1702_ = lean_ctor_get_uint8(v_env_1700_, sizeof(void*)*13);
if (v_isExporting_1702_ == 0)
{
lean_object* v___x_1703_; 
lean_dec_ref(v_env_1700_);
lean_dec(v_declHint_1695_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_msg_1694_);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
lean_inc_ref(v_env_1700_);
v___x_1704_ = l_Lean_Environment_setExporting(v_env_1700_, v___x_1701_);
lean_inc(v_declHint_1695_);
lean_inc_ref(v___x_1704_);
v___x_1705_ = l_Lean_Environment_contains(v___x_1704_, v_declHint_1695_, v_isExporting_1702_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref(v___x_1704_);
lean_dec_ref(v_env_1700_);
lean_dec(v_declHint_1695_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_msg_1694_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_c_1712_; lean_object* v___x_1713_; 
v___x_1707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2);
v___x_1708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5);
v___x_1709_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1704_);
v___x_1710_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1704_);
lean_ctor_set(v___x_1710_, 1, v___x_1707_);
lean_ctor_set(v___x_1710_, 2, v___x_1708_);
lean_ctor_set(v___x_1710_, 3, v___x_1709_);
lean_inc(v_declHint_1695_);
v___x_1711_ = l_Lean_MessageData_ofConstName(v_declHint_1695_, v___x_1701_);
v_c_1712_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1712_, 0, v___x_1710_);
lean_ctor_set(v_c_1712_, 1, v___x_1711_);
v___x_1713_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1704_, v_declHint_1695_);
lean_dec_ref(v___x_1704_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref(v_env_1700_);
lean_dec(v_declHint_1695_);
v___x_1714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v_c_1712_);
v___x_1716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_MessageData_note(v___x_1717_);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_msg_1694_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
else
{
lean_object* v_val_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1755_; 
v_val_1721_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1723_ = v___x_1713_;
v_isShared_1724_ = v_isSharedCheck_1755_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_val_1721_);
lean_dec(v___x_1713_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1755_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v_moduleNames_1726_; lean_object* v_mod_1727_; uint8_t v___x_1728_; 
v___x_1725_ = l_Lean_Environment_header(v_env_1700_);
lean_dec_ref(v_env_1700_);
v_moduleNames_1726_ = lean_ctor_get(v___x_1725_, 4);
lean_inc_ref(v_moduleNames_1726_);
lean_dec_ref(v___x_1725_);
v_mod_1727_ = lean_array_get(v___x_1698_, v_moduleNames_1726_, v_val_1721_);
lean_dec(v_val_1721_);
lean_dec_ref(v_moduleNames_1726_);
v___x_1728_ = l_Lean_isPrivateName(v_declHint_1695_);
lean_dec(v_declHint_1695_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_c_1712_);
v___x_1731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_MessageData_ofName(v_mod_1727_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_MessageData_note(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_msg_1694_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1738_);
v___x_1740_ = v___x_1723_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_c_1712_);
v___x_1744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_MessageData_ofName(v_mod_1727_);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_MessageData_note(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_msg_1694_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1751_);
v___x_1753_ = v___x_1723_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1756_; 
lean_dec_ref(v_env_1700_);
lean_dec(v_declHint_1695_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v_msg_1694_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___boxed(lean_object* v_msg_1757_, lean_object* v_declHint_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_1757_, v_declHint_1758_, v___y_1759_);
lean_dec(v___y_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(lean_object* v_msg_1762_, lean_object* v_declHint_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1779_; 
v___x_1769_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_1762_, v_declHint_1763_, v___y_1767_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1774_ = l_Lean_unknownIdentifierMessageTag;
v___x_1775_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v_a_1770_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24___boxed(lean_object* v_msg_1780_, lean_object* v_declHint_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(v_msg_1780_, v_declHint_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(lean_object* v_ref_1788_, lean_object* v_msg_1789_, lean_object* v_declHint_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1798_; 
v___x_1796_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(v_msg_1789_, v_declHint_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_1788_, v_a_1797_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg___boxed(lean_object* v_ref_1799_, lean_object* v_msg_1800_, lean_object* v_declHint_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_1799_, v_msg_1800_, v_declHint_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v_ref_1799_);
return v_res_1807_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(lean_object* v_ref_1814_, lean_object* v_constName_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1821_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1);
v___x_1822_ = 0;
lean_inc(v_constName_1815_);
v___x_1823_ = l_Lean_MessageData_ofConstName(v_constName_1815_, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1821_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_1814_, v___x_1826_, v_constName_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1828_, lean_object* v_constName_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_1828_, v_constName_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v_ref_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_ref_1842_; lean_object* v___x_1843_; 
v_ref_1842_ = lean_ctor_get(v___y_1839_, 2);
v___x_1843_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_1842_, v_constName_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v_env_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1857_ = lean_st_ref_get(v___y_1855_);
v_env_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc_ref(v_env_1858_);
lean_dec(v___x_1857_);
v___x_1859_ = 0;
lean_inc(v_constName_1851_);
v___x_1860_ = l_Lean_Environment_findConstVal_x3f(v_env_1858_, v_constName_1851_, v___x_1859_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_constName_1851_);
v_val_1862_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1860_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_val_1862_);
lean_dec(v___x_1860_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_val_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v___dummy_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_1883_, uint8_t v_isExporting_1884_, lean_object* v___x_1885_, lean_object* v___y_1886_, lean_object* v___x_1887_, lean_object* v_a_x3f_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_env_1891_; lean_object* v_nextMacroScope_1892_; lean_object* v_ngen_1893_; lean_object* v_auxDeclNGen_1894_; lean_object* v_traceState_1895_; lean_object* v_recordedDeps_1896_; lean_object* v_messages_1897_; lean_object* v_infoState_1898_; lean_object* v_snapshotTasks_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1924_; 
v___x_1890_ = lean_st_ref_take(v___y_1883_);
v_env_1891_ = lean_ctor_get(v___x_1890_, 0);
v_nextMacroScope_1892_ = lean_ctor_get(v___x_1890_, 1);
v_ngen_1893_ = lean_ctor_get(v___x_1890_, 2);
v_auxDeclNGen_1894_ = lean_ctor_get(v___x_1890_, 3);
v_traceState_1895_ = lean_ctor_get(v___x_1890_, 4);
v_recordedDeps_1896_ = lean_ctor_get(v___x_1890_, 6);
v_messages_1897_ = lean_ctor_get(v___x_1890_, 7);
v_infoState_1898_ = lean_ctor_get(v___x_1890_, 8);
v_snapshotTasks_1899_ = lean_ctor_get(v___x_1890_, 9);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1890_, 5);
lean_dec(v_unused_1925_);
v___x_1901_ = v___x_1890_;
v_isShared_1902_ = v_isSharedCheck_1924_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snapshotTasks_1899_);
lean_inc(v_infoState_1898_);
lean_inc(v_messages_1897_);
lean_inc(v_recordedDeps_1896_);
lean_inc(v_traceState_1895_);
lean_inc(v_auxDeclNGen_1894_);
lean_inc(v_ngen_1893_);
lean_inc(v_nextMacroScope_1892_);
lean_inc(v_env_1891_);
lean_dec(v___x_1890_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1924_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = l_Lean_Environment_setExporting(v_env_1891_, v_isExporting_1884_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 5, v___x_1885_);
lean_ctor_set(v___x_1901_, 0, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_nextMacroScope_1892_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_ngen_1893_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_auxDeclNGen_1894_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_traceState_1895_);
lean_ctor_set(v_reuseFailAlloc_1923_, 5, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1923_, 6, v_recordedDeps_1896_);
lean_ctor_set(v_reuseFailAlloc_1923_, 7, v_messages_1897_);
lean_ctor_set(v_reuseFailAlloc_1923_, 8, v_infoState_1898_);
lean_ctor_set(v_reuseFailAlloc_1923_, 9, v_snapshotTasks_1899_);
v___x_1905_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_mctx_1908_; lean_object* v_zetaDeltaFVarIds_1909_; lean_object* v_postponed_1910_; lean_object* v_diag_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1921_; 
v___x_1906_ = lean_st_ref_put(v___y_1883_, v___x_1905_);
v___x_1907_ = lean_st_ref_take(v___y_1886_);
v_mctx_1908_ = lean_ctor_get(v___x_1907_, 0);
v_zetaDeltaFVarIds_1909_ = lean_ctor_get(v___x_1907_, 2);
v_postponed_1910_ = lean_ctor_get(v___x_1907_, 3);
v_diag_1911_ = lean_ctor_get(v___x_1907_, 4);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___x_1907_, 1);
lean_dec(v_unused_1922_);
v___x_1913_ = v___x_1907_;
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_diag_1911_);
lean_inc(v_postponed_1910_);
lean_inc(v_zetaDeltaFVarIds_1909_);
lean_inc(v_mctx_1908_);
lean_dec(v___x_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = lean_box(0);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___x_1887_);
v___x_1917_ = v___x_1913_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_mctx_1908_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_zetaDeltaFVarIds_1909_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_postponed_1910_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_diag_1911_);
v___x_1917_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_st_ref_put(v___y_1886_, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1915_);
return v___x_1919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_1926_, lean_object* v_isExporting_1927_, lean_object* v___x_1928_, lean_object* v___y_1929_, lean_object* v___x_1930_, lean_object* v_a_x3f_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v_isExporting_boxed_1933_; lean_object* v_res_1934_; 
v_isExporting_boxed_1933_ = lean_unbox(v_isExporting_1927_);
v_res_1934_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1926_, v_isExporting_boxed_1933_, v___x_1928_, v___y_1929_, v___x_1930_, v_a_x3f_1931_);
lean_dec(v_a_x3f_1931_);
lean_dec(v___y_1929_);
lean_dec(v___y_1926_);
return v_res_1934_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1941_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_1942_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
lean_ctor_set(v___x_1942_, 2, v___x_1940_);
lean_ctor_set(v___x_1942_, 3, v___x_1940_);
lean_ctor_set(v___x_1942_, 4, v___x_1940_);
lean_ctor_set(v___x_1942_, 5, v___x_1940_);
lean_ctor_set(v___x_1942_, 6, v___x_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_1943_, uint8_t v_isExporting_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v_env_1951_; lean_object* v___x_1952_; uint8_t v_isModule_1953_; 
v___x_1950_ = lean_st_ref_get(v___y_1948_);
v_env_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc_ref(v_env_1951_);
lean_dec(v___x_1950_);
v___x_1952_ = l_Lean_Environment_header(v_env_1951_);
v_isModule_1953_ = lean_ctor_get_uint8(v___x_1952_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1952_);
if (v_isModule_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref(v_env_1951_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v___x_1954_ = lean_apply_5(v_x_1943_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
return v___x_1954_;
}
else
{
uint8_t v_isExporting_1955_; 
v_isExporting_1955_ = lean_ctor_get_uint8(v_env_1951_, sizeof(void*)*13);
lean_dec_ref(v_env_1951_);
if (v_isExporting_1944_ == 0)
{
if (v_isExporting_1955_ == 0)
{
lean_object* v___x_2022_; 
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v___x_2022_ = lean_apply_5(v_x_1943_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
return v___x_2022_;
}
else
{
goto v___jp_1956_;
}
}
else
{
if (v_isExporting_1955_ == 0)
{
goto v___jp_1956_;
}
else
{
lean_object* v___x_2023_; 
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v___x_2023_ = lean_apply_5(v_x_1943_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
return v___x_2023_;
}
}
v___jp_1956_:
{
lean_object* v___x_1957_; lean_object* v_env_1958_; lean_object* v_nextMacroScope_1959_; lean_object* v_ngen_1960_; lean_object* v_auxDeclNGen_1961_; lean_object* v_traceState_1962_; lean_object* v_recordedDeps_1963_; lean_object* v_messages_1964_; lean_object* v_infoState_1965_; lean_object* v_snapshotTasks_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2020_; 
v___x_1957_ = lean_st_ref_take(v___y_1948_);
v_env_1958_ = lean_ctor_get(v___x_1957_, 0);
v_nextMacroScope_1959_ = lean_ctor_get(v___x_1957_, 1);
v_ngen_1960_ = lean_ctor_get(v___x_1957_, 2);
v_auxDeclNGen_1961_ = lean_ctor_get(v___x_1957_, 3);
v_traceState_1962_ = lean_ctor_get(v___x_1957_, 4);
v_recordedDeps_1963_ = lean_ctor_get(v___x_1957_, 6);
v_messages_1964_ = lean_ctor_get(v___x_1957_, 7);
v_infoState_1965_ = lean_ctor_get(v___x_1957_, 8);
v_snapshotTasks_1966_ = lean_ctor_get(v___x_1957_, 9);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_1957_, 5);
lean_dec(v_unused_2021_);
v___x_1968_ = v___x_1957_;
v_isShared_1969_ = v_isSharedCheck_2020_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snapshotTasks_1966_);
lean_inc(v_infoState_1965_);
lean_inc(v_messages_1964_);
lean_inc(v_recordedDeps_1963_);
lean_inc(v_traceState_1962_);
lean_inc(v_auxDeclNGen_1961_);
lean_inc(v_ngen_1960_);
lean_inc(v_nextMacroScope_1959_);
lean_inc(v_env_1958_);
lean_dec(v___x_1957_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2020_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1970_ = l_Lean_Environment_setExporting(v_env_1958_, v_isExporting_1944_);
v___x_1971_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 5, v___x_1971_);
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1973_ = v___x_1968_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_nextMacroScope_1959_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_ngen_1960_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_auxDeclNGen_1961_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_traceState_1962_);
lean_ctor_set(v_reuseFailAlloc_2019_, 5, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_2019_, 6, v_recordedDeps_1963_);
lean_ctor_set(v_reuseFailAlloc_2019_, 7, v_messages_1964_);
lean_ctor_set(v_reuseFailAlloc_2019_, 8, v_infoState_1965_);
lean_ctor_set(v_reuseFailAlloc_2019_, 9, v_snapshotTasks_1966_);
v___x_1973_ = v_reuseFailAlloc_2019_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_mctx_1976_; lean_object* v_zetaDeltaFVarIds_1977_; lean_object* v_postponed_1978_; lean_object* v_diag_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2017_; 
v___x_1974_ = lean_st_ref_put(v___y_1948_, v___x_1973_);
v___x_1975_ = lean_st_ref_take(v___y_1946_);
v_mctx_1976_ = lean_ctor_get(v___x_1975_, 0);
v_zetaDeltaFVarIds_1977_ = lean_ctor_get(v___x_1975_, 2);
v_postponed_1978_ = lean_ctor_get(v___x_1975_, 3);
v_diag_1979_ = lean_ctor_get(v___x_1975_, 4);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v___x_1975_, 1);
lean_dec(v_unused_2018_);
v___x_1981_ = v___x_1975_;
v_isShared_1982_ = v_isSharedCheck_2017_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_diag_1979_);
lean_inc(v_postponed_1978_);
lean_inc(v_zetaDeltaFVarIds_1977_);
lean_inc(v_mctx_1976_);
lean_dec(v___x_1975_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2017_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 1, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_mctx_1976_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_zetaDeltaFVarIds_1977_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_postponed_1978_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_diag_1979_);
v___x_1985_ = v_reuseFailAlloc_2016_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v_r_1987_; 
v___x_1986_ = lean_st_ref_put(v___y_1946_, v___x_1985_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v_r_1987_ = lean_apply_5(v_x_1943_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
if (lean_obj_tag(v_r_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2004_; 
v_a_1988_ = lean_ctor_get(v_r_1987_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_r_1987_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1990_ = v_r_1987_;
v_isShared_1991_ = v_isSharedCheck_2004_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v_r_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2004_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
lean_inc(v_a_1988_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 1);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v___x_1994_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1948_, v_isExporting_1955_, v___x_1971_, v___y_1946_, v___x_1983_, v___x_1993_);
lean_dec_ref(v___x_1993_);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v___x_1994_, 0);
lean_dec(v_unused_2002_);
v___x_1996_ = v___x_1994_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_dec(v___x_1994_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v_a_1988_);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1988_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2005_ = lean_ctor_get(v_r_1987_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v_r_1987_, 1);
v___x_2006_ = lean_box(0);
v___x_2007_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1948_, v_isExporting_1955_, v___x_1971_, v___y_1946_, v___x_1983_, v___x_2006_);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; 
v_unused_2015_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2015_);
v___x_2009_ = v___x_2007_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v___x_2007_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 1);
lean_ctor_set(v___x_2009_, 0, v_a_2005_);
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2005_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_2024_, lean_object* v_isExporting_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
uint8_t v_isExporting_boxed_2031_; lean_object* v_res_2032_; 
v_isExporting_boxed_2031_ = lean_unbox(v_isExporting_2025_);
v_res_2032_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_2024_, v_isExporting_boxed_2031_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0(lean_object* v_addEntryFn_2033_, lean_object* v_decl_2034_, lean_object* v_s_2035_){
_start:
{
lean_object* v_importedEntries_2036_; lean_object* v_state_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2045_; 
v_importedEntries_2036_ = lean_ctor_get(v_s_2035_, 0);
v_state_2037_ = lean_ctor_get(v_s_2035_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_s_2035_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2039_ = v_s_2035_;
v_isShared_2040_ = v_isSharedCheck_2045_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_state_2037_);
lean_inc(v_importedEntries_2036_);
lean_dec(v_s_2035_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2045_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_state_2041_; lean_object* v___x_2043_; 
v_state_2041_ = lean_apply_2(v_addEntryFn_2033_, v_state_2037_, v_decl_2034_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 1, v_state_2041_);
v___x_2043_ = v___x_2039_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_importedEntries_2036_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_state_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2));
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_attrName_2055_, lean_object* v_declName_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2062_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1);
v___x_2063_ = l_Lean_MessageData_ofName(v_attrName_2055_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = 0;
v___x_2068_ = l_Lean_MessageData_ofConstName(v_declName_2056_, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2066_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_2071_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_attrName_2073_, lean_object* v_declName_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_attrName_2073_, v_declName_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2080_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(lean_object* v_attrName_2087_, lean_object* v_declName_2088_, lean_object* v_asyncPrefix_x3f_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___y_2096_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2089_) == 0)
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_MessageData_nil;
v___y_2096_ = v___x_2109_;
goto v___jp_2095_;
}
else
{
lean_object* v_val_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_val_2110_ = lean_ctor_get(v_asyncPrefix_x3f_2089_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v_asyncPrefix_x3f_2089_, 1);
v___x_2111_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3);
v___x_2112_ = l_Lean_MessageData_ofName(v_val_2110_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___y_2096_ = v___x_2115_;
goto v___jp_2095_;
}
v___jp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2097_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1);
v___x_2098_ = l_Lean_MessageData_ofName(v_attrName_2087_);
v___x_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = 0;
v___x_2103_ = l_Lean_MessageData_ofConstName(v_declName_2088_, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2101_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___y_2096_);
v___x_2108_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_2107_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___boxed(lean_object* v_attrName_2116_, lean_object* v_declName_2117_, lean_object* v_asyncPrefix_x3f_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_attrName_2116_, v_declName_2117_, v_asyncPrefix_x3f_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_attr_2125_, lean_object* v_decl_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___x_2187_; lean_object* v_env_2188_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___x_2203_; 
v___x_2187_ = lean_st_ref_get(v___y_2130_);
v_env_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc_ref(v_env_2188_);
lean_dec(v___x_2187_);
v___x_2203_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2188_, v_decl_2126_);
if (lean_obj_tag(v___x_2203_) == 0)
{
v___y_2190_ = v___y_2127_;
v___y_2191_ = v___y_2128_;
v___y_2192_ = v___y_2129_;
v___y_2193_ = v___y_2130_;
goto v___jp_2189_;
}
else
{
lean_object* v_attr_2204_; lean_object* v_toAttributeImplCore_2205_; lean_object* v_name_2206_; lean_object* v___x_2207_; 
lean_dec_ref_known(v___x_2203_, 1);
lean_dec_ref(v_env_2188_);
v_attr_2204_ = lean_ctor_get(v_attr_2125_, 0);
lean_inc_ref(v_attr_2204_);
lean_dec_ref(v_attr_2125_);
v_toAttributeImplCore_2205_ = lean_ctor_get(v_attr_2204_, 0);
lean_inc_ref(v_toAttributeImplCore_2205_);
lean_dec_ref(v_attr_2204_);
v_name_2206_ = lean_ctor_get(v_toAttributeImplCore_2205_, 1);
lean_inc(v_name_2206_);
lean_dec_ref(v_toAttributeImplCore_2205_);
v___x_2207_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_name_2206_, v_decl_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2207_;
}
v___jp_2132_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_mctx_2148_; lean_object* v_zetaDeltaFVarIds_2149_; lean_object* v_postponed_2150_; lean_object* v_diag_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2162_; 
v___x_2144_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_2145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2145_, 0, v___y_2143_);
lean_ctor_set(v___x_2145_, 1, v___y_2138_);
lean_ctor_set(v___x_2145_, 2, v___y_2136_);
lean_ctor_set(v___x_2145_, 3, v___y_2142_);
lean_ctor_set(v___x_2145_, 4, v___y_2140_);
lean_ctor_set(v___x_2145_, 5, v___x_2144_);
lean_ctor_set(v___x_2145_, 6, v___y_2139_);
lean_ctor_set(v___x_2145_, 7, v___y_2137_);
lean_ctor_set(v___x_2145_, 8, v___y_2135_);
lean_ctor_set(v___x_2145_, 9, v___y_2134_);
v___x_2146_ = lean_st_ref_put(v___y_2141_, v___x_2145_);
v___x_2147_ = lean_st_ref_take(v___y_2133_);
v_mctx_2148_ = lean_ctor_get(v___x_2147_, 0);
v_zetaDeltaFVarIds_2149_ = lean_ctor_get(v___x_2147_, 2);
v_postponed_2150_ = lean_ctor_get(v___x_2147_, 3);
v_diag_2151_ = lean_ctor_get(v___x_2147_, 4);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v___x_2147_, 1);
lean_dec(v_unused_2163_);
v___x_2153_ = v___x_2147_;
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_diag_2151_);
lean_inc(v_postponed_2150_);
lean_inc(v_zetaDeltaFVarIds_2149_);
lean_inc(v_mctx_2148_);
lean_dec(v___x_2147_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2156_);
v___x_2158_ = v___x_2153_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_mctx_2148_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_zetaDeltaFVarIds_2149_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_postponed_2150_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_diag_2151_);
v___x_2158_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_st_ref_put(v___y_2133_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2155_);
return v___x_2160_;
}
}
}
v___jp_2164_:
{
lean_object* v___x_2167_; lean_object* v_ext_2168_; lean_object* v_toEnvExtension_2169_; lean_object* v_env_2170_; lean_object* v_nextMacroScope_2171_; lean_object* v_ngen_2172_; lean_object* v_auxDeclNGen_2173_; lean_object* v_traceState_2174_; lean_object* v_recordedDeps_2175_; lean_object* v_messages_2176_; lean_object* v_infoState_2177_; lean_object* v_snapshotTasks_2178_; lean_object* v_addEntryFn_2179_; lean_object* v_asyncMode_2180_; uint8_t v_logWrites_2181_; lean_object* v___f_2182_; uint8_t v___x_2183_; 
v___x_2167_ = lean_st_ref_take(v___y_2166_);
v_ext_2168_ = lean_ctor_get(v_attr_2125_, 1);
lean_inc_ref(v_ext_2168_);
lean_dec_ref(v_attr_2125_);
v_toEnvExtension_2169_ = lean_ctor_get(v_ext_2168_, 0);
lean_inc_ref(v_toEnvExtension_2169_);
v_env_2170_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_env_2170_);
v_nextMacroScope_2171_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_nextMacroScope_2171_);
v_ngen_2172_ = lean_ctor_get(v___x_2167_, 2);
lean_inc_ref(v_ngen_2172_);
v_auxDeclNGen_2173_ = lean_ctor_get(v___x_2167_, 3);
lean_inc_ref(v_auxDeclNGen_2173_);
v_traceState_2174_ = lean_ctor_get(v___x_2167_, 4);
lean_inc_ref(v_traceState_2174_);
v_recordedDeps_2175_ = lean_ctor_get(v___x_2167_, 6);
lean_inc_ref(v_recordedDeps_2175_);
v_messages_2176_ = lean_ctor_get(v___x_2167_, 7);
lean_inc_ref(v_messages_2176_);
v_infoState_2177_ = lean_ctor_get(v___x_2167_, 8);
lean_inc_ref(v_infoState_2177_);
v_snapshotTasks_2178_ = lean_ctor_get(v___x_2167_, 9);
lean_inc_ref(v_snapshotTasks_2178_);
lean_dec(v___x_2167_);
v_addEntryFn_2179_ = lean_ctor_get(v_ext_2168_, 3);
lean_inc(v_addEntryFn_2179_);
lean_dec_ref(v_ext_2168_);
v_asyncMode_2180_ = lean_ctor_get(v_toEnvExtension_2169_, 2);
lean_inc(v_asyncMode_2180_);
v_logWrites_2181_ = lean_ctor_get_uint8(v_toEnvExtension_2169_, sizeof(void*)*6);
lean_inc(v_decl_2126_);
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0), 3, 2);
lean_closure_set(v___f_2182_, 0, v_addEntryFn_2179_);
lean_closure_set(v___f_2182_, 1, v_decl_2126_);
v___x_2183_ = 1;
if (v_logWrites_2181_ == 0)
{
lean_object* v___x_2184_; 
v___x_2184_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2169_, v_env_2170_, v___f_2182_, v_asyncMode_2180_, v_decl_2126_, v___x_2183_);
lean_dec(v_asyncMode_2180_);
v___y_2133_ = v___y_2165_;
v___y_2134_ = v_snapshotTasks_2178_;
v___y_2135_ = v_infoState_2177_;
v___y_2136_ = v_ngen_2172_;
v___y_2137_ = v_messages_2176_;
v___y_2138_ = v_nextMacroScope_2171_;
v___y_2139_ = v_recordedDeps_2175_;
v___y_2140_ = v_traceState_2174_;
v___y_2141_ = v___y_2166_;
v___y_2142_ = v_auxDeclNGen_2173_;
v___y_2143_ = v___x_2184_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_inc_ref(v_toEnvExtension_2169_);
v___x_2185_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2169_, v_env_2170_);
lean_dec_ref(v_env_2170_);
v___x_2186_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2169_, v___x_2185_, v___f_2182_, v_asyncMode_2180_, v_decl_2126_, v___x_2183_);
lean_dec(v_asyncMode_2180_);
v___y_2133_ = v___y_2165_;
v___y_2134_ = v_snapshotTasks_2178_;
v___y_2135_ = v_infoState_2177_;
v___y_2136_ = v_ngen_2172_;
v___y_2137_ = v_messages_2176_;
v___y_2138_ = v_nextMacroScope_2171_;
v___y_2139_ = v_recordedDeps_2175_;
v___y_2140_ = v_traceState_2174_;
v___y_2141_ = v___y_2166_;
v___y_2142_ = v_auxDeclNGen_2173_;
v___y_2143_ = v___x_2186_;
goto v___jp_2132_;
}
}
v___jp_2189_:
{
lean_object* v_ext_2194_; lean_object* v_toEnvExtension_2195_; lean_object* v_attr_2196_; lean_object* v_asyncMode_2197_; uint8_t v___x_2198_; 
v_ext_2194_ = lean_ctor_get(v_attr_2125_, 1);
v_toEnvExtension_2195_ = lean_ctor_get(v_ext_2194_, 0);
v_attr_2196_ = lean_ctor_get(v_attr_2125_, 0);
v_asyncMode_2197_ = lean_ctor_get(v_toEnvExtension_2195_, 2);
lean_inc(v_decl_2126_);
lean_inc_ref(v_env_2188_);
v___x_2198_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2188_, v_decl_2126_, v_asyncMode_2197_);
if (v___x_2198_ == 0)
{
lean_object* v_toAttributeImplCore_2199_; lean_object* v_name_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_inc_ref(v_attr_2196_);
lean_dec_ref(v_attr_2125_);
v_toAttributeImplCore_2199_ = lean_ctor_get(v_attr_2196_, 0);
lean_inc_ref(v_toAttributeImplCore_2199_);
lean_dec_ref(v_attr_2196_);
v_name_2200_ = lean_ctor_get(v_toAttributeImplCore_2199_, 1);
lean_inc(v_name_2200_);
lean_dec_ref(v_toAttributeImplCore_2199_);
v___x_2201_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2188_);
v___x_2202_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_name_2200_, v_decl_2126_, v___x_2201_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2202_;
}
else
{
lean_dec_ref(v_env_2188_);
v___y_2165_ = v___y_2191_;
v___y_2166_ = v___y_2193_;
goto v___jp_2164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_attr_2208_, lean_object* v_decl_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_attr_2208_, v_decl_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v_env_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
v___x_2222_ = lean_st_ref_get(v___y_2220_);
v_env_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc_ref(v_env_2223_);
lean_dec(v___x_2222_);
v___x_2224_ = 0;
lean_inc(v_constName_2216_);
v___x_2225_ = l_Lean_Environment_find_x3f(v_env_2223_, v_constName_2216_, v___x_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2226_;
}
else
{
lean_object* v_val_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_constName_2216_);
v_val_2227_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2225_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_val_2227_);
lean_dec(v___x_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 0);
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_val_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(lean_object* v_declName_2242_, uint8_t v_s_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v_env_2248_; lean_object* v_nextMacroScope_2249_; lean_object* v_ngen_2250_; lean_object* v_auxDeclNGen_2251_; lean_object* v_traceState_2252_; lean_object* v_recordedDeps_2253_; lean_object* v_messages_2254_; lean_object* v_infoState_2255_; lean_object* v_snapshotTasks_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2285_; 
v___x_2247_ = lean_st_ref_take(v___y_2245_);
v_env_2248_ = lean_ctor_get(v___x_2247_, 0);
v_nextMacroScope_2249_ = lean_ctor_get(v___x_2247_, 1);
v_ngen_2250_ = lean_ctor_get(v___x_2247_, 2);
v_auxDeclNGen_2251_ = lean_ctor_get(v___x_2247_, 3);
v_traceState_2252_ = lean_ctor_get(v___x_2247_, 4);
v_recordedDeps_2253_ = lean_ctor_get(v___x_2247_, 6);
v_messages_2254_ = lean_ctor_get(v___x_2247_, 7);
v_infoState_2255_ = lean_ctor_get(v___x_2247_, 8);
v_snapshotTasks_2256_ = lean_ctor_get(v___x_2247_, 9);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2247_, 5);
lean_dec(v_unused_2286_);
v___x_2258_ = v___x_2247_;
v_isShared_2259_ = v_isSharedCheck_2285_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_snapshotTasks_2256_);
lean_inc(v_infoState_2255_);
lean_inc(v_messages_2254_);
lean_inc(v_recordedDeps_2253_);
lean_inc(v_traceState_2252_);
lean_inc(v_auxDeclNGen_2251_);
lean_inc(v_ngen_2250_);
lean_inc(v_nextMacroScope_2249_);
lean_inc(v_env_2248_);
lean_dec(v___x_2247_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2285_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2260_ = 0;
v___x_2261_ = lean_box(0);
v___x_2262_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2248_, v_declName_2242_, v_s_2243_, v___x_2260_, v___x_2261_);
v___x_2263_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 5, v___x_2263_);
lean_ctor_set(v___x_2258_, 0, v___x_2262_);
v___x_2265_ = v___x_2258_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_nextMacroScope_2249_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_ngen_2250_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_auxDeclNGen_2251_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_traceState_2252_);
lean_ctor_set(v_reuseFailAlloc_2284_, 5, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2284_, 6, v_recordedDeps_2253_);
lean_ctor_set(v_reuseFailAlloc_2284_, 7, v_messages_2254_);
lean_ctor_set(v_reuseFailAlloc_2284_, 8, v_infoState_2255_);
lean_ctor_set(v_reuseFailAlloc_2284_, 9, v_snapshotTasks_2256_);
v___x_2265_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v_mctx_2268_; lean_object* v_zetaDeltaFVarIds_2269_; lean_object* v_postponed_2270_; lean_object* v_diag_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2282_; 
v___x_2266_ = lean_st_ref_put(v___y_2245_, v___x_2265_);
v___x_2267_ = lean_st_ref_take(v___y_2244_);
v_mctx_2268_ = lean_ctor_get(v___x_2267_, 0);
v_zetaDeltaFVarIds_2269_ = lean_ctor_get(v___x_2267_, 2);
v_postponed_2270_ = lean_ctor_get(v___x_2267_, 3);
v_diag_2271_ = lean_ctor_get(v___x_2267_, 4);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2267_, 1);
lean_dec(v_unused_2283_);
v___x_2273_ = v___x_2267_;
v_isShared_2274_ = v_isSharedCheck_2282_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_diag_2271_);
lean_inc(v_postponed_2270_);
lean_inc(v_zetaDeltaFVarIds_2269_);
lean_inc(v_mctx_2268_);
lean_dec(v___x_2267_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2282_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v___x_2276_);
v___x_2278_ = v___x_2273_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_mctx_2268_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_zetaDeltaFVarIds_2269_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_postponed_2270_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_diag_2271_);
v___x_2278_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_st_ref_put(v___y_2244_, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2275_);
return v___x_2280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg___boxed(lean_object* v_declName_2287_, lean_object* v_s_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_s_boxed_2292_; lean_object* v_res_2293_; 
v_s_boxed_2292_ = lean_unbox(v_s_2288_);
v_res_2293_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2287_, v_s_boxed_2292_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec(v___y_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_declName_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = 0;
v___x_2301_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2294_, v___x_2300_, v___y_2296_, v___y_2298_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_declName_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_declName_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2308_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2312_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2313_ = lean_unsigned_to_nat(58u);
v___x_2314_ = lean_unsigned_to_nat(33u);
v___x_2315_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2316_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2317_ = l_mkPanicMessageWithDecl(v___x_2316_, v___x_2315_, v___x_2314_, v___x_2313_, v___x_2312_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2319_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2320_ = lean_unsigned_to_nat(60u);
v___x_2321_ = lean_unsigned_to_nat(30u);
v___x_2322_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2323_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2324_ = l_mkPanicMessageWithDecl(v___x_2323_, v___x_2322_, v___x_2321_, v___x_2320_, v___x_2319_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2325_, lean_object* v_indName_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; 
lean_inc(v_indName_2326_);
v___x_2332_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
if (lean_obj_tag(v_a_2333_) == 5)
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2524_; 
v_val_2334_ = lean_ctor_get(v_a_2333_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2333_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2336_ = v_a_2333_;
v_isShared_2337_ = v_isSharedCheck_2524_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v_a_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2524_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_inc(v_indName_2326_);
v___x_2338_ = l_Lean_mkCasesOnName(v_indName_2326_);
lean_inc(v___x_2338_);
v___x_2339_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2338_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v_name_2341_; lean_object* v_levelParams_2342_; lean_object* v_type_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v_name_2341_ = lean_ctor_get(v_a_2340_, 0);
lean_inc(v_name_2341_);
v_levelParams_2342_ = lean_ctor_get(v_a_2340_, 1);
lean_inc_n(v_levelParams_2342_, 2);
v_type_2343_ = lean_ctor_get(v_a_2340_, 2);
lean_inc_ref(v_type_2343_);
lean_dec(v_a_2340_);
v___x_2344_ = lean_box(0);
v___x_2345_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2342_, v___x_2344_);
if (lean_obj_tag(v___x_2345_) == 1)
{
lean_object* v_head_2346_; lean_object* v_tail_2347_; lean_object* v_numParams_2348_; lean_object* v_numIndices_2349_; lean_object* v_ctors_2350_; lean_object* v___f_2351_; lean_object* v___x_2353_; 
v_head_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_head_2346_);
v_tail_2347_ = lean_ctor_get(v___x_2345_, 1);
lean_inc(v_tail_2347_);
v_numParams_2348_ = lean_ctor_get(v_val_2334_, 1);
lean_inc_n(v_numParams_2348_, 2);
v_numIndices_2349_ = lean_ctor_get(v_val_2334_, 2);
lean_inc(v_numIndices_2349_);
v_ctors_2350_ = lean_ctor_get(v_val_2334_, 4);
lean_inc(v_ctors_2350_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2351_, 0, v_numIndices_2349_);
lean_closure_set(v___f_2351_, 1, v_head_2346_);
lean_closure_set(v___f_2351_, 2, v_ctors_2350_);
lean_closure_set(v___f_2351_, 3, v_indName_2326_);
lean_closure_set(v___f_2351_, 4, v_tail_2347_);
lean_closure_set(v___f_2351_, 5, v_name_2341_);
lean_closure_set(v___f_2351_, 6, v___x_2345_);
lean_closure_set(v___f_2351_, 7, v_numParams_2348_);
lean_closure_set(v___f_2351_, 8, v_val_2334_);
lean_closure_set(v___f_2351_, 9, v___x_2338_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 1);
lean_ctor_set(v___x_2336_, 0, v_numParams_2348_);
v___x_2353_ = v___x_2336_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_numParams_2348_);
v___x_2353_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
uint8_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = 0;
v___x_2355_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2343_, v___x_2353_, v___f_2351_, v___x_2354_, v___x_2354_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; uint8_t v___y_2360_; uint8_t v___x_2503_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2357_ = lean_box(v___x_2354_);
lean_inc(v_declName_2325_);
v___f_2358_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2358_, 0, v_a_2356_);
lean_closure_set(v___f_2358_, 1, v_declName_2325_);
lean_closure_set(v___f_2358_, 2, v_levelParams_2342_);
lean_closure_set(v___f_2358_, 3, v___x_2357_);
v___x_2503_ = l_Lean_isPrivateName(v_declName_2325_);
if (v___x_2503_ == 0)
{
uint8_t v___x_2504_; 
v___x_2504_ = 1;
v___y_2360_ = v___x_2504_;
goto v___jp_2359_;
}
else
{
v___y_2360_ = v___x_2354_;
goto v___jp_2359_;
}
v___jp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2358_, v___y_2360_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2362_; lean_object* v_env_2363_; lean_object* v_nextMacroScope_2364_; lean_object* v_ngen_2365_; lean_object* v_auxDeclNGen_2366_; lean_object* v_traceState_2367_; lean_object* v_recordedDeps_2368_; lean_object* v_messages_2369_; lean_object* v_infoState_2370_; lean_object* v_snapshotTasks_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2501_; 
lean_dec_ref_known(v___x_2361_, 1);
v___x_2362_ = lean_st_ref_take(v_a_2330_);
v_env_2363_ = lean_ctor_get(v___x_2362_, 0);
v_nextMacroScope_2364_ = lean_ctor_get(v___x_2362_, 1);
v_ngen_2365_ = lean_ctor_get(v___x_2362_, 2);
v_auxDeclNGen_2366_ = lean_ctor_get(v___x_2362_, 3);
v_traceState_2367_ = lean_ctor_get(v___x_2362_, 4);
v_recordedDeps_2368_ = lean_ctor_get(v___x_2362_, 6);
v_messages_2369_ = lean_ctor_get(v___x_2362_, 7);
v_infoState_2370_ = lean_ctor_get(v___x_2362_, 8);
v_snapshotTasks_2371_ = lean_ctor_get(v___x_2362_, 9);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2362_, 5);
lean_dec(v_unused_2502_);
v___x_2373_ = v___x_2362_;
v_isShared_2374_ = v_isSharedCheck_2501_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_snapshotTasks_2371_);
lean_inc(v_infoState_2370_);
lean_inc(v_messages_2369_);
lean_inc(v_recordedDeps_2368_);
lean_inc(v_traceState_2367_);
lean_inc(v_auxDeclNGen_2366_);
lean_inc(v_ngen_2365_);
lean_inc(v_nextMacroScope_2364_);
lean_inc(v_env_2363_);
lean_dec(v___x_2362_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2501_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_inc(v_declName_2325_);
v___x_2375_ = l_Lean_Meta_markMatcherLike(v_env_2363_, v_declName_2325_);
v___x_2376_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 5, v___x_2376_);
lean_ctor_set(v___x_2373_, 0, v___x_2375_);
v___x_2378_ = v___x_2373_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_nextMacroScope_2364_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_ngen_2365_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_auxDeclNGen_2366_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v_traceState_2367_);
lean_ctor_set(v_reuseFailAlloc_2500_, 5, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2500_, 6, v_recordedDeps_2368_);
lean_ctor_set(v_reuseFailAlloc_2500_, 7, v_messages_2369_);
lean_ctor_set(v_reuseFailAlloc_2500_, 8, v_infoState_2370_);
lean_ctor_set(v_reuseFailAlloc_2500_, 9, v_snapshotTasks_2371_);
v___x_2378_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v_mctx_2381_; lean_object* v_zetaDeltaFVarIds_2382_; lean_object* v_postponed_2383_; lean_object* v_diag_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2498_; 
v___x_2379_ = lean_st_ref_put(v_a_2330_, v___x_2378_);
v___x_2380_ = lean_st_ref_take(v_a_2328_);
v_mctx_2381_ = lean_ctor_get(v___x_2380_, 0);
v_zetaDeltaFVarIds_2382_ = lean_ctor_get(v___x_2380_, 2);
v_postponed_2383_ = lean_ctor_get(v___x_2380_, 3);
v_diag_2384_ = lean_ctor_get(v___x_2380_, 4);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2380_, 1);
lean_dec(v_unused_2499_);
v___x_2386_ = v___x_2380_;
v_isShared_2387_ = v_isSharedCheck_2498_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_diag_2384_);
lean_inc(v_postponed_2383_);
lean_inc(v_zetaDeltaFVarIds_2382_);
lean_inc(v_mctx_2381_);
lean_dec(v___x_2380_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2498_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2388_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v___x_2388_);
v___x_2390_ = v___x_2386_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_mctx_2381_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_zetaDeltaFVarIds_2382_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_postponed_2383_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_diag_2384_);
v___x_2390_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_env_2393_; lean_object* v_nextMacroScope_2394_; lean_object* v_ngen_2395_; lean_object* v_auxDeclNGen_2396_; lean_object* v_traceState_2397_; lean_object* v_recordedDeps_2398_; lean_object* v_messages_2399_; lean_object* v_infoState_2400_; lean_object* v_snapshotTasks_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2495_; 
v___x_2391_ = lean_st_ref_put(v_a_2328_, v___x_2390_);
v___x_2392_ = lean_st_ref_take(v_a_2330_);
v_env_2393_ = lean_ctor_get(v___x_2392_, 0);
v_nextMacroScope_2394_ = lean_ctor_get(v___x_2392_, 1);
v_ngen_2395_ = lean_ctor_get(v___x_2392_, 2);
v_auxDeclNGen_2396_ = lean_ctor_get(v___x_2392_, 3);
v_traceState_2397_ = lean_ctor_get(v___x_2392_, 4);
v_recordedDeps_2398_ = lean_ctor_get(v___x_2392_, 6);
v_messages_2399_ = lean_ctor_get(v___x_2392_, 7);
v_infoState_2400_ = lean_ctor_get(v___x_2392_, 8);
v_snapshotTasks_2401_ = lean_ctor_get(v___x_2392_, 9);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2392_, 5);
lean_dec(v_unused_2496_);
v___x_2403_ = v___x_2392_;
v_isShared_2404_ = v_isSharedCheck_2495_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_snapshotTasks_2401_);
lean_inc(v_infoState_2400_);
lean_inc(v_messages_2399_);
lean_inc(v_recordedDeps_2398_);
lean_inc(v_traceState_2397_);
lean_inc(v_auxDeclNGen_2396_);
lean_inc(v_ngen_2395_);
lean_inc(v_nextMacroScope_2394_);
lean_inc(v_env_2393_);
lean_dec(v___x_2392_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2495_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2407_; 
lean_inc(v_declName_2325_);
v___x_2405_ = l_Lean_markAuxRecursor(v_env_2393_, v_declName_2325_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 5, v___x_2376_);
lean_ctor_set(v___x_2403_, 0, v___x_2405_);
v___x_2407_ = v___x_2403_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_nextMacroScope_2394_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_ngen_2395_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_auxDeclNGen_2396_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_traceState_2397_);
lean_ctor_set(v_reuseFailAlloc_2494_, 5, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_recordedDeps_2398_);
lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_messages_2399_);
lean_ctor_set(v_reuseFailAlloc_2494_, 8, v_infoState_2400_);
lean_ctor_set(v_reuseFailAlloc_2494_, 9, v_snapshotTasks_2401_);
v___x_2407_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v_mctx_2410_; lean_object* v_zetaDeltaFVarIds_2411_; lean_object* v_postponed_2412_; lean_object* v_diag_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2492_; 
v___x_2408_ = lean_st_ref_put(v_a_2330_, v___x_2407_);
v___x_2409_ = lean_st_ref_take(v_a_2328_);
v_mctx_2410_ = lean_ctor_get(v___x_2409_, 0);
v_zetaDeltaFVarIds_2411_ = lean_ctor_get(v___x_2409_, 2);
v_postponed_2412_ = lean_ctor_get(v___x_2409_, 3);
v_diag_2413_ = lean_ctor_get(v___x_2409_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2409_, 1);
lean_dec(v_unused_2493_);
v___x_2415_ = v___x_2409_;
v_isShared_2416_ = v_isSharedCheck_2492_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_diag_2413_);
lean_inc(v_postponed_2412_);
lean_inc(v_zetaDeltaFVarIds_2411_);
lean_inc(v_mctx_2410_);
lean_dec(v___x_2409_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2492_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v___x_2388_);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_mctx_2410_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_zetaDeltaFVarIds_2411_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_postponed_2412_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_diag_2413_);
v___x_2418_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v_env_2421_; lean_object* v_nextMacroScope_2422_; lean_object* v_ngen_2423_; lean_object* v_auxDeclNGen_2424_; lean_object* v_traceState_2425_; lean_object* v_recordedDeps_2426_; lean_object* v_messages_2427_; lean_object* v_infoState_2428_; lean_object* v_snapshotTasks_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2489_; 
v___x_2419_ = lean_st_ref_put(v_a_2328_, v___x_2418_);
v___x_2420_ = lean_st_ref_take(v_a_2330_);
v_env_2421_ = lean_ctor_get(v___x_2420_, 0);
v_nextMacroScope_2422_ = lean_ctor_get(v___x_2420_, 1);
v_ngen_2423_ = lean_ctor_get(v___x_2420_, 2);
v_auxDeclNGen_2424_ = lean_ctor_get(v___x_2420_, 3);
v_traceState_2425_ = lean_ctor_get(v___x_2420_, 4);
v_recordedDeps_2426_ = lean_ctor_get(v___x_2420_, 6);
v_messages_2427_ = lean_ctor_get(v___x_2420_, 7);
v_infoState_2428_ = lean_ctor_get(v___x_2420_, 8);
v_snapshotTasks_2429_ = lean_ctor_get(v___x_2420_, 9);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2420_, 5);
lean_dec(v_unused_2490_);
v___x_2431_ = v___x_2420_;
v_isShared_2432_ = v_isSharedCheck_2489_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snapshotTasks_2429_);
lean_inc(v_infoState_2428_);
lean_inc(v_messages_2427_);
lean_inc(v_recordedDeps_2426_);
lean_inc(v_traceState_2425_);
lean_inc(v_auxDeclNGen_2424_);
lean_inc(v_ngen_2423_);
lean_inc(v_nextMacroScope_2422_);
lean_inc(v_env_2421_);
lean_dec(v___x_2420_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2489_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
lean_inc(v_declName_2325_);
v___x_2433_ = l_Lean_Meta_addToCompletionBlackList(v_env_2421_, v_declName_2325_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 5, v___x_2376_);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_nextMacroScope_2422_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_ngen_2423_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_auxDeclNGen_2424_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_traceState_2425_);
lean_ctor_set(v_reuseFailAlloc_2488_, 5, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_recordedDeps_2426_);
lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_messages_2427_);
lean_ctor_set(v_reuseFailAlloc_2488_, 8, v_infoState_2428_);
lean_ctor_set(v_reuseFailAlloc_2488_, 9, v_snapshotTasks_2429_);
v___x_2435_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_mctx_2438_; lean_object* v_zetaDeltaFVarIds_2439_; lean_object* v_postponed_2440_; lean_object* v_diag_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2486_; 
v___x_2436_ = lean_st_ref_put(v_a_2330_, v___x_2435_);
v___x_2437_ = lean_st_ref_take(v_a_2328_);
v_mctx_2438_ = lean_ctor_get(v___x_2437_, 0);
v_zetaDeltaFVarIds_2439_ = lean_ctor_get(v___x_2437_, 2);
v_postponed_2440_ = lean_ctor_get(v___x_2437_, 3);
v_diag_2441_ = lean_ctor_get(v___x_2437_, 4);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2437_, 1);
lean_dec(v_unused_2487_);
v___x_2443_ = v___x_2437_;
v_isShared_2444_ = v_isSharedCheck_2486_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_diag_2441_);
lean_inc(v_postponed_2440_);
lean_inc(v_zetaDeltaFVarIds_2439_);
lean_inc(v_mctx_2438_);
lean_dec(v___x_2437_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2486_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v___x_2388_);
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_mctx_2438_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_zetaDeltaFVarIds_2439_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_postponed_2440_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_diag_2441_);
v___x_2446_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_env_2449_; lean_object* v_nextMacroScope_2450_; lean_object* v_ngen_2451_; lean_object* v_auxDeclNGen_2452_; lean_object* v_traceState_2453_; lean_object* v_recordedDeps_2454_; lean_object* v_messages_2455_; lean_object* v_infoState_2456_; lean_object* v_snapshotTasks_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2483_; 
v___x_2447_ = lean_st_ref_put(v_a_2328_, v___x_2446_);
v___x_2448_ = lean_st_ref_take(v_a_2330_);
v_env_2449_ = lean_ctor_get(v___x_2448_, 0);
v_nextMacroScope_2450_ = lean_ctor_get(v___x_2448_, 1);
v_ngen_2451_ = lean_ctor_get(v___x_2448_, 2);
v_auxDeclNGen_2452_ = lean_ctor_get(v___x_2448_, 3);
v_traceState_2453_ = lean_ctor_get(v___x_2448_, 4);
v_recordedDeps_2454_ = lean_ctor_get(v___x_2448_, 6);
v_messages_2455_ = lean_ctor_get(v___x_2448_, 7);
v_infoState_2456_ = lean_ctor_get(v___x_2448_, 8);
v_snapshotTasks_2457_ = lean_ctor_get(v___x_2448_, 9);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2448_, 5);
lean_dec(v_unused_2484_);
v___x_2459_ = v___x_2448_;
v_isShared_2460_ = v_isSharedCheck_2483_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_snapshotTasks_2457_);
lean_inc(v_infoState_2456_);
lean_inc(v_messages_2455_);
lean_inc(v_recordedDeps_2454_);
lean_inc(v_traceState_2453_);
lean_inc(v_auxDeclNGen_2452_);
lean_inc(v_ngen_2451_);
lean_inc(v_nextMacroScope_2450_);
lean_inc(v_env_2449_);
lean_dec(v___x_2448_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2483_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_inc(v_declName_2325_);
v___x_2461_ = l_Lean_addProtected(v_env_2449_, v_declName_2325_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 5, v___x_2376_);
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_nextMacroScope_2450_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_ngen_2451_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_auxDeclNGen_2452_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_traceState_2453_);
lean_ctor_set(v_reuseFailAlloc_2482_, 5, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2482_, 6, v_recordedDeps_2454_);
lean_ctor_set(v_reuseFailAlloc_2482_, 7, v_messages_2455_);
lean_ctor_set(v_reuseFailAlloc_2482_, 8, v_infoState_2456_);
lean_ctor_set(v_reuseFailAlloc_2482_, 9, v_snapshotTasks_2457_);
v___x_2463_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v_mctx_2466_; lean_object* v_zetaDeltaFVarIds_2467_; lean_object* v_postponed_2468_; lean_object* v_diag_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2480_; 
v___x_2464_ = lean_st_ref_put(v_a_2330_, v___x_2463_);
v___x_2465_ = lean_st_ref_take(v_a_2328_);
v_mctx_2466_ = lean_ctor_get(v___x_2465_, 0);
v_zetaDeltaFVarIds_2467_ = lean_ctor_get(v___x_2465_, 2);
v_postponed_2468_ = lean_ctor_get(v___x_2465_, 3);
v_diag_2469_ = lean_ctor_get(v___x_2465_, 4);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2465_, 1);
lean_dec(v_unused_2481_);
v___x_2471_ = v___x_2465_;
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_diag_2469_);
lean_inc(v_postponed_2468_);
lean_inc(v_zetaDeltaFVarIds_2467_);
lean_inc(v_mctx_2466_);
lean_dec(v___x_2465_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2388_);
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_mctx_2466_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_zetaDeltaFVarIds_2467_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_postponed_2468_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_diag_2469_);
v___x_2474_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = lean_st_ref_put(v_a_2328_, v___x_2474_);
v___x_2476_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2325_);
v___x_2477_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v___x_2476_, v_declName_2325_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v___x_2478_; 
lean_dec_ref_known(v___x_2477_, 1);
v___x_2478_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_declName_2325_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2478_;
}
else
{
lean_dec(v_declName_2325_);
return v___x_2477_;
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
lean_dec(v_declName_2325_);
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_levelParams_2342_);
lean_dec(v_declName_2325_);
v_a_2505_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2355_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2355_);
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
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v___x_2345_);
lean_dec_ref(v_type_2343_);
lean_dec(v_levelParams_2342_);
lean_dec(v_name_2341_);
lean_dec(v___x_2338_);
lean_del_object(v___x_2336_);
lean_dec_ref(v_val_2334_);
lean_dec(v_indName_2326_);
lean_dec(v_declName_2325_);
v___x_2514_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2515_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_2514_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2515_;
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v___x_2338_);
lean_del_object(v___x_2336_);
lean_dec_ref(v_val_2334_);
lean_dec(v_indName_2326_);
lean_dec(v_declName_2325_);
v_a_2516_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2339_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2339_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec(v_a_2333_);
lean_dec(v_indName_2326_);
lean_dec(v_declName_2325_);
v___x_2525_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2526_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_2525_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2526_;
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_indName_2326_);
lean_dec(v_declName_2325_);
v_a_2527_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2332_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2332_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2535_, lean_object* v_indName_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2535_, v_indName_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2543_, lean_object* v_name_2544_, lean_object* v_type_2545_, lean_object* v_k_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2544_, v_type_2545_, v_k_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2553_, lean_object* v_name_2554_, lean_object* v_type_2555_, lean_object* v_k_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2553_, v_name_2554_, v_type_2555_, v_k_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2563_, lean_object* v_params_2564_, lean_object* v_alts_2565_, lean_object* v___x_2566_, lean_object* v_ism2_2567_, lean_object* v_motive_2568_, lean_object* v_val_2569_, lean_object* v_indName_2570_, lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v___x_2573_, lean_object* v_as_2574_, size_t v_sz_2575_, size_t v_i_2576_, lean_object* v_bs_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2563_, v_params_2564_, v_alts_2565_, v___x_2566_, v_ism2_2567_, v_motive_2568_, v_val_2569_, v_indName_2570_, v___x_2571_, v___x_2572_, v___x_2573_, v_sz_2575_, v_i_2576_, v_bs_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2584_ = _args[0];
lean_object* v_params_2585_ = _args[1];
lean_object* v_alts_2586_ = _args[2];
lean_object* v___x_2587_ = _args[3];
lean_object* v_ism2_2588_ = _args[4];
lean_object* v_motive_2589_ = _args[5];
lean_object* v_val_2590_ = _args[6];
lean_object* v_indName_2591_ = _args[7];
lean_object* v___x_2592_ = _args[8];
lean_object* v___x_2593_ = _args[9];
lean_object* v___x_2594_ = _args[10];
lean_object* v_as_2595_ = _args[11];
lean_object* v_sz_2596_ = _args[12];
lean_object* v_i_2597_ = _args[13];
lean_object* v_bs_2598_ = _args[14];
lean_object* v___y_2599_ = _args[15];
lean_object* v___y_2600_ = _args[16];
lean_object* v___y_2601_ = _args[17];
lean_object* v___y_2602_ = _args[18];
lean_object* v___y_2603_ = _args[19];
_start:
{
size_t v_sz_boxed_2604_; size_t v_i_boxed_2605_; lean_object* v_res_2606_; 
v_sz_boxed_2604_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2605_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2606_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2584_, v_params_2585_, v_alts_2586_, v___x_2587_, v_ism2_2588_, v_motive_2589_, v_val_2590_, v_indName_2591_, v___x_2592_, v___x_2593_, v___x_2594_, v_as_2595_, v_sz_boxed_2604_, v_i_boxed_2605_, v_bs_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v_as_2595_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2607_, lean_object* v_params_2608_, lean_object* v___x_2609_, lean_object* v_motive_2610_, lean_object* v_as_2611_, size_t v_sz_2612_, size_t v_i_2613_, lean_object* v_bs_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2607_, v_params_2608_, v___x_2609_, v_motive_2610_, v_sz_2612_, v_i_2613_, v_bs_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2621_, lean_object* v_params_2622_, lean_object* v___x_2623_, lean_object* v_motive_2624_, lean_object* v_as_2625_, lean_object* v_sz_2626_, lean_object* v_i_2627_, lean_object* v_bs_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
size_t v_sz_boxed_2634_; size_t v_i_boxed_2635_; lean_object* v_res_2636_; 
v_sz_boxed_2634_ = lean_unbox_usize(v_sz_2626_);
lean_dec(v_sz_2626_);
v_i_boxed_2635_ = lean_unbox_usize(v_i_2627_);
lean_dec(v_i_2627_);
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2621_, v_params_2622_, v___x_2623_, v_motive_2624_, v_as_2625_, v_sz_boxed_2634_, v_i_boxed_2635_, v_bs_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v_as_2625_);
lean_dec_ref(v_params_2622_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_2637_, lean_object* v_x_2638_, uint8_t v_isExporting_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_2638_, v_isExporting_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_x_2647_, lean_object* v_isExporting_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
uint8_t v_isExporting_boxed_2654_; lean_object* v_res_2655_; 
v_isExporting_boxed_2654_ = lean_unbox(v_isExporting_2648_);
v_res_2655_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_2646_, v_x_2647_, v_isExporting_boxed_2654_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b2_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg(){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg___boxed(lean_object* v___dummy_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg();
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_00_u03b2_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2664_, lean_object* v_constName_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2672_, lean_object* v_constName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2672_, v_constName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(lean_object* v_00_u03b1_2680_, lean_object* v_attrName_2681_, lean_object* v_declName_2682_, lean_object* v_asyncPrefix_x3f_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_attrName_2681_, v_declName_2682_, v_asyncPrefix_x3f_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___boxed(lean_object* v_00_u03b1_2690_, lean_object* v_attrName_2691_, lean_object* v_declName_2692_, lean_object* v_asyncPrefix_x3f_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(v_00_u03b1_2690_, v_attrName_2691_, v_declName_2692_, v_asyncPrefix_x3f_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_00_u03b1_2700_, lean_object* v_attrName_2701_, lean_object* v_declName_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_attrName_2701_, v_declName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_attrName_2710_, lean_object* v_declName_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_00_u03b1_2709_, v_attrName_2710_, v_declName_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(lean_object* v_declName_2718_, uint8_t v_s_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2718_, v_s_2719_, v___y_2721_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___boxed(lean_object* v_declName_2726_, lean_object* v_s_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v_s_boxed_2733_; lean_object* v_res_2734_; 
v_s_boxed_2733_ = lean_unbox(v_s_2727_);
v_res_2734_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(v_declName_2726_, v_s_boxed_2733_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(lean_object* v_00_u03b1_2735_, lean_object* v_ref_2736_, lean_object* v_constName_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_2736_, v_constName_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2744_, lean_object* v_ref_2745_, lean_object* v_constName_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(v_00_u03b1_2744_, v_ref_2745_, v_constName_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v_ref_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(lean_object* v_00_u03b1_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_msg_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(v_00_u03b1_2761_, v_msg_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(lean_object* v_00_u03b1_2769_, lean_object* v_ref_2770_, lean_object* v_msg_2771_, lean_object* v_declHint_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_2770_, v_msg_2771_, v_declHint_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_ref_2780_, lean_object* v_msg_2781_, lean_object* v_declHint_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(v_00_u03b1_2779_, v_ref_2780_, v_msg_2781_, v_declHint_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v_ref_2780_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(lean_object* v_msg_2789_, lean_object* v_declHint_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_2789_, v_declHint_2790_, v___y_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___boxed(lean_object* v_msg_2797_, lean_object* v_declHint_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(v_msg_2797_, v_declHint_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(lean_object* v_00_u03b1_2805_, lean_object* v_ref_2806_, lean_object* v_msg_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_2806_, v_msg_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_ref_2815_, lean_object* v_msg_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(v_00_u03b1_2814_, v_ref_2815_, v_msg_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v_ref_2815_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v___x_2826_; 
v___x_2826_ = l_Lean_Expr_hasMVar(v_e_2823_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_e_2823_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; lean_object* v_mctx_2829_; lean_object* v___x_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v___x_2833_; lean_object* v_cache_2834_; lean_object* v_zetaDeltaFVarIds_2835_; lean_object* v_postponed_2836_; lean_object* v_diag_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2846_; 
v___x_2828_ = lean_st_ref_get(v___y_2824_);
v_mctx_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_mctx_2829_);
lean_dec(v___x_2828_);
v___x_2830_ = l_Lean_instantiateMVarsCore(v_mctx_2829_, v_e_2823_);
v_fst_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_fst_2831_);
v_snd_2832_ = lean_ctor_get(v___x_2830_, 1);
lean_inc(v_snd_2832_);
lean_dec_ref(v___x_2830_);
v___x_2833_ = lean_st_ref_take(v___y_2824_);
v_cache_2834_ = lean_ctor_get(v___x_2833_, 1);
v_zetaDeltaFVarIds_2835_ = lean_ctor_get(v___x_2833_, 2);
v_postponed_2836_ = lean_ctor_get(v___x_2833_, 3);
v_diag_2837_ = lean_ctor_get(v___x_2833_, 4);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2833_, 0);
lean_dec(v_unused_2847_);
v___x_2839_ = v___x_2833_;
v_isShared_2840_ = v_isSharedCheck_2846_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_diag_2837_);
lean_inc(v_postponed_2836_);
lean_inc(v_zetaDeltaFVarIds_2835_);
lean_inc(v_cache_2834_);
lean_dec(v___x_2833_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2846_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v_snd_2832_);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_snd_2832_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_cache_2834_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_zetaDeltaFVarIds_2835_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_postponed_2836_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_diag_2837_);
v___x_2842_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_st_ref_put(v___y_2824_, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_fst_2831_);
return v___x_2844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2848_, v___y_2849_);
lean_dec(v___y_2849_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2852_, v___y_2854_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2866_, lean_object* v___x_2867_, lean_object* v_newEqs1_2868_, uint8_t v___x_2869_, uint8_t v___x_2870_, uint8_t v___x_2871_, lean_object* v_ism1_x27_2872_, lean_object* v_ism2_x27_2873_, lean_object* v_newRefls1_2874_, lean_object* v_newEqs2_2875_, lean_object* v_newRefls2_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = l_Lean_mkAppN(v_motive_2866_, v___x_2867_);
v___x_2883_ = l_Array_append___redArg(v_newEqs1_2868_, v_newEqs2_2875_);
v___x_2884_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v___x_2882_, v___x_2869_, v___x_2870_, v___x_2870_, v___x_2871_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = l_Array_append___redArg(v_ism1_x27_2872_, v_ism2_x27_2873_);
v___x_2887_ = l_Lean_Meta_mkLambdaFVars(v___x_2886_, v_a_2885_, v___x_2869_, v___x_2870_, v___x_2869_, v___x_2870_, v___x_2871_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v___x_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2897_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2897_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2897_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2892_ = l_Array_append___redArg(v_newRefls1_2874_, v_newRefls2_2876_);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_a_2888_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2893_);
v___x_2895_ = v___x_2890_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_newRefls1_2874_);
v_a_2898_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2887_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2887_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v_newRefls1_2874_);
lean_dec_ref(v_ism1_x27_2872_);
v_a_2906_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2884_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2884_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2914_, lean_object* v___x_2915_, lean_object* v_newEqs1_2916_, lean_object* v___x_2917_, lean_object* v___x_2918_, lean_object* v___x_2919_, lean_object* v_ism1_x27_2920_, lean_object* v_ism2_x27_2921_, lean_object* v_newRefls1_2922_, lean_object* v_newEqs2_2923_, lean_object* v_newRefls2_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
uint8_t v___x_14898__boxed_2930_; uint8_t v___x_14899__boxed_2931_; uint8_t v___x_14900__boxed_2932_; lean_object* v_res_2933_; 
v___x_14898__boxed_2930_ = lean_unbox(v___x_2917_);
v___x_14899__boxed_2931_ = lean_unbox(v___x_2918_);
v___x_14900__boxed_2932_ = lean_unbox(v___x_2919_);
v_res_2933_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2914_, v___x_2915_, v_newEqs1_2916_, v___x_14898__boxed_2930_, v___x_14899__boxed_2931_, v___x_14900__boxed_2932_, v_ism1_x27_2920_, v_ism2_x27_2921_, v_newRefls1_2922_, v_newEqs2_2923_, v_newRefls2_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec_ref(v_newRefls2_2924_);
lean_dec_ref(v_newEqs2_2923_);
lean_dec_ref(v_ism2_x27_2921_);
lean_dec_ref(v___x_2915_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2934_, lean_object* v___x_2935_, uint8_t v___x_2936_, uint8_t v___x_2937_, uint8_t v___x_2938_, lean_object* v_ism1_x27_2939_, lean_object* v_ism2_x27_2940_, lean_object* v_is_2941_, lean_object* v___x_2942_, lean_object* v_newEqs1_2943_, lean_object* v_newRefls1_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2950_ = lean_box(v___x_2936_);
v___x_2951_ = lean_box(v___x_2937_);
v___x_2952_ = lean_box(v___x_2938_);
lean_inc_ref(v_ism2_x27_2940_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2953_, 0, v_motive_2934_);
lean_closure_set(v___f_2953_, 1, v___x_2935_);
lean_closure_set(v___f_2953_, 2, v_newEqs1_2943_);
lean_closure_set(v___f_2953_, 3, v___x_2950_);
lean_closure_set(v___f_2953_, 4, v___x_2951_);
lean_closure_set(v___f_2953_, 5, v___x_2952_);
lean_closure_set(v___f_2953_, 6, v_ism1_x27_2939_);
lean_closure_set(v___f_2953_, 7, v_ism2_x27_2940_);
lean_closure_set(v___f_2953_, 8, v_newRefls1_2944_);
v___x_2954_ = lean_array_push(v_is_2941_, v___x_2942_);
v___x_2955_ = l_Lean_Meta_withNewEqs___redArg(v___x_2954_, v_ism2_x27_2940_, v___f_2953_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2956_, lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v_ism1_x27_2961_, lean_object* v_ism2_x27_2962_, lean_object* v_is_2963_, lean_object* v___x_2964_, lean_object* v_newEqs1_2965_, lean_object* v_newRefls1_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
uint8_t v___x_14989__boxed_2972_; uint8_t v___x_14990__boxed_2973_; uint8_t v___x_14991__boxed_2974_; lean_object* v_res_2975_; 
v___x_14989__boxed_2972_ = lean_unbox(v___x_2958_);
v___x_14990__boxed_2973_ = lean_unbox(v___x_2959_);
v___x_14991__boxed_2974_ = lean_unbox(v___x_2960_);
v_res_2975_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2956_, v___x_2957_, v___x_14989__boxed_2972_, v___x_14990__boxed_2973_, v___x_14991__boxed_2974_, v_ism1_x27_2961_, v_ism2_x27_2962_, v_is_2963_, v___x_2964_, v_newEqs1_2965_, v_newRefls1_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2976_, uint8_t v___x_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_addDecl(v___x_2976_, v___x_2977_, v___y_2980_, v___y_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_2984_, lean_object* v___x_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
uint8_t v___x_15031__boxed_2991_; lean_object* v_res_2992_; 
v___x_15031__boxed_2991_ = lean_unbox(v___x_2985_);
v_res_2992_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_2984_, v___x_15031__boxed_2991_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2993_, lean_object* v_info_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v_env_2999_; lean_object* v_nextMacroScope_3000_; lean_object* v_ngen_3001_; lean_object* v_auxDeclNGen_3002_; lean_object* v_traceState_3003_; lean_object* v_recordedDeps_3004_; lean_object* v_messages_3005_; lean_object* v_infoState_3006_; lean_object* v_snapshotTasks_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3034_; 
v___x_2998_ = lean_st_ref_take(v___y_2996_);
v_env_2999_ = lean_ctor_get(v___x_2998_, 0);
v_nextMacroScope_3000_ = lean_ctor_get(v___x_2998_, 1);
v_ngen_3001_ = lean_ctor_get(v___x_2998_, 2);
v_auxDeclNGen_3002_ = lean_ctor_get(v___x_2998_, 3);
v_traceState_3003_ = lean_ctor_get(v___x_2998_, 4);
v_recordedDeps_3004_ = lean_ctor_get(v___x_2998_, 6);
v_messages_3005_ = lean_ctor_get(v___x_2998_, 7);
v_infoState_3006_ = lean_ctor_get(v___x_2998_, 8);
v_snapshotTasks_3007_ = lean_ctor_get(v___x_2998_, 9);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v___x_2998_, 5);
lean_dec(v_unused_3035_);
v___x_3009_ = v___x_2998_;
v_isShared_3010_ = v_isSharedCheck_3034_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snapshotTasks_3007_);
lean_inc(v_infoState_3006_);
lean_inc(v_messages_3005_);
lean_inc(v_recordedDeps_3004_);
lean_inc(v_traceState_3003_);
lean_inc(v_auxDeclNGen_3002_);
lean_inc(v_ngen_3001_);
lean_inc(v_nextMacroScope_3000_);
lean_inc(v_env_2999_);
lean_dec(v___x_2998_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3034_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3011_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2999_, v_matcherName_2993_, v_info_2994_);
v___x_3012_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 5, v___x_3012_);
lean_ctor_set(v___x_3009_, 0, v___x_3011_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_nextMacroScope_3000_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_ngen_3001_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_auxDeclNGen_3002_);
lean_ctor_set(v_reuseFailAlloc_3033_, 4, v_traceState_3003_);
lean_ctor_set(v_reuseFailAlloc_3033_, 5, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3033_, 6, v_recordedDeps_3004_);
lean_ctor_set(v_reuseFailAlloc_3033_, 7, v_messages_3005_);
lean_ctor_set(v_reuseFailAlloc_3033_, 8, v_infoState_3006_);
lean_ctor_set(v_reuseFailAlloc_3033_, 9, v_snapshotTasks_3007_);
v___x_3014_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v_mctx_3017_; lean_object* v_zetaDeltaFVarIds_3018_; lean_object* v_postponed_3019_; lean_object* v_diag_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3031_; 
v___x_3015_ = lean_st_ref_put(v___y_2996_, v___x_3014_);
v___x_3016_ = lean_st_ref_take(v___y_2995_);
v_mctx_3017_ = lean_ctor_get(v___x_3016_, 0);
v_zetaDeltaFVarIds_3018_ = lean_ctor_get(v___x_3016_, 2);
v_postponed_3019_ = lean_ctor_get(v___x_3016_, 3);
v_diag_3020_ = lean_ctor_get(v___x_3016_, 4);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v___x_3016_, 1);
lean_dec(v_unused_3032_);
v___x_3022_ = v___x_3016_;
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_diag_3020_);
lean_inc(v_postponed_3019_);
lean_inc(v_zetaDeltaFVarIds_3018_);
lean_inc(v_mctx_3017_);
lean_dec(v___x_3016_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3025_);
v___x_3027_ = v___x_3022_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_mctx_3017_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_zetaDeltaFVarIds_3018_);
lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_postponed_3019_);
lean_ctor_set(v_reuseFailAlloc_3030_, 4, v_diag_3020_);
v___x_3027_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_st_ref_put(v___y_2995_, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3024_);
return v___x_3029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_3036_, lean_object* v_info_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_3036_, v_info_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec(v___y_3038_);
return v_res_3041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3044_ = l_Lean_stringToMessageData(v___x_3043_);
return v___x_3044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
v___x_3054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3055_ = l_Lean_mkConst(v___x_3054_, v___x_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3059_, lean_object* v_a_3060_, lean_object* v___x_3061_, lean_object* v_zs1_3062_, lean_object* v_snd_3063_, uint8_t v___x_3064_, uint8_t v___x_3065_, uint8_t v___x_3066_, lean_object* v_alts_3067_, lean_object* v_zs2_3068_, lean_object* v___ctorRet2_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_array_get_borrowed(v___x_3059_, v_a_3060_, v___x_3061_);
lean_inc_ref(v_zs1_3062_);
v___x_3076_ = l_Array_append___redArg(v_zs1_3062_, v_zs2_3068_);
lean_inc(v___x_3075_);
v___x_3077_ = l_Lean_Meta_instantiateForall(v___x_3075_, v___x_3076_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = lean_box(0);
v___x_3080_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3078_, v___x_3079_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Expr_mvarId_x21(v_a_3081_);
v___x_3083_ = lean_array_get_size(v_snd_3063_);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_box(0);
lean_inc_ref(v___y_3072_);
v___x_3086_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3083_, v___x_3082_, v___x_3084_, v___x_3085_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
if (lean_obj_tag(v_a_3087_) == 1)
{
lean_object* v_val_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3135_; 
v_val_3088_ = lean_ctor_get(v_a_3087_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3087_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3090_ = v_a_3087_;
v_isShared_3091_ = v_isSharedCheck_3135_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_val_3088_);
lean_dec(v_a_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3135_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_fst_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3133_; 
v_fst_3092_ = lean_ctor_get(v_val_3088_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_val_3088_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_val_3088_, 1);
lean_dec(v_unused_3134_);
v___x_3094_ = v_val_3088_;
v_isShared_3095_ = v_isSharedCheck_3133_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_fst_3092_);
lean_dec(v_val_3088_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3133_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___y_3097_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3125_ = lean_array_get_borrowed(v___x_3059_, v_alts_3067_, v___x_3061_);
v___x_3126_ = lean_array_get_size(v_zs1_3062_);
lean_dec_ref(v_zs1_3062_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_nat_dec_eq(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_inc(v___x_3125_);
v___y_3097_ = v___x_3125_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = lean_array_get_size(v_zs2_3068_);
v___x_3130_ = lean_nat_dec_eq(v___x_3129_, v___x_3127_);
if (v___x_3130_ == 0)
{
lean_inc(v___x_3125_);
v___y_3097_ = v___x_3125_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3125_);
v___x_3132_ = l_Lean_Expr_app___override(v___x_3125_, v___x_3131_);
v___y_3097_ = v___x_3132_;
goto v___jp_3096_;
}
}
v___jp_3096_:
{
uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = 0;
v___x_3099_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3099_, 0, v___x_3098_);
lean_ctor_set_uint8(v___x_3099_, 1, v___x_3064_);
lean_ctor_set_uint8(v___x_3099_, 2, v___x_3065_);
lean_ctor_set_uint8(v___x_3099_, 3, v___x_3064_);
lean_inc_ref(v___y_3097_);
lean_inc(v_fst_3092_);
v___x_3100_ = l_Lean_MVarId_apply(v_fst_3092_, v___y_3097_, v___x_3099_, v___x_3085_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
if (lean_obj_tag(v_a_3101_) == 0)
{
lean_object* v___x_3102_; 
lean_dec_ref(v___y_3097_);
lean_del_object(v___x_3094_);
lean_dec(v_fst_3092_);
lean_del_object(v___x_3090_);
v___x_3102_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3081_, v___y_3071_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = l_Lean_Meta_mkLambdaFVars(v___x_3076_, v_a_3103_, v___x_3065_, v___x_3064_, v___x_3065_, v___x_3064_, v___x_3066_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec_ref(v___x_3076_);
return v___x_3104_;
}
else
{
lean_dec_ref(v___x_3076_);
return v___x_3102_;
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_dec(v_a_3101_);
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
v___x_3105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3106_ = l_Lean_MessageData_ofExpr(v___y_3097_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 7);
lean_ctor_set(v___x_3094_, 1, v___x_3106_);
lean_ctor_set(v___x_3094_, 0, v___x_3105_);
v___x_3108_ = v___x_3094_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v_fst_3092_);
v___x_3112_ = v___x_3090_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_fst_3092_);
v___x_3112_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3110_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_3113_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v___y_3097_);
lean_del_object(v___x_3094_);
lean_dec(v_fst_3092_);
lean_del_object(v___x_3090_);
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
v_a_3117_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3100_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3100_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_a_3087_);
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
v___x_3136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3137_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_3136_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3137_;
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
v_a_3138_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3086_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3086_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
return v___x_3080_;
}
}
else
{
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3146_, lean_object* v_a_3147_, lean_object* v___x_3148_, lean_object* v_zs1_3149_, lean_object* v_snd_3150_, lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v___x_3153_, lean_object* v_alts_3154_, lean_object* v_zs2_3155_, lean_object* v___ctorRet2_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v___x_15168__boxed_3162_; uint8_t v___x_15169__boxed_3163_; uint8_t v___x_15170__boxed_3164_; lean_object* v_res_3165_; 
v___x_15168__boxed_3162_ = lean_unbox(v___x_3151_);
v___x_15169__boxed_3163_ = lean_unbox(v___x_3152_);
v___x_15170__boxed_3164_ = lean_unbox(v___x_3153_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3146_, v_a_3147_, v___x_3148_, v_zs1_3149_, v_snd_3150_, v___x_15168__boxed_3162_, v___x_15169__boxed_3163_, v___x_15170__boxed_3164_, v_alts_3154_, v_zs2_3155_, v___ctorRet2_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec_ref(v___ctorRet2_3156_);
lean_dec_ref(v_zs2_3155_);
lean_dec_ref(v_alts_3154_);
lean_dec_ref(v_snd_3150_);
lean_dec(v___x_3148_);
lean_dec_ref(v_a_3147_);
lean_dec_ref(v___x_3146_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3166_, lean_object* v_a_3167_, lean_object* v___x_3168_, lean_object* v_snd_3169_, uint8_t v___x_3170_, uint8_t v___x_3171_, uint8_t v___x_3172_, lean_object* v_alts_3173_, lean_object* v_a_3174_, lean_object* v_zs1_3175_, lean_object* v___ctorRet1_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; 
v___x_3182_ = lean_box(v___x_3170_);
v___x_3183_ = lean_box(v___x_3171_);
v___x_3184_ = lean_box(v___x_3172_);
v___f_3185_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3185_, 0, v___x_3166_);
lean_closure_set(v___f_3185_, 1, v_a_3167_);
lean_closure_set(v___f_3185_, 2, v___x_3168_);
lean_closure_set(v___f_3185_, 3, v_zs1_3175_);
lean_closure_set(v___f_3185_, 4, v_snd_3169_);
lean_closure_set(v___f_3185_, 5, v___x_3182_);
lean_closure_set(v___f_3185_, 6, v___x_3183_);
lean_closure_set(v___f_3185_, 7, v___x_3184_);
lean_closure_set(v___f_3185_, 8, v_alts_3173_);
v___x_3186_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3174_, v___f_3185_, v___x_3171_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3187_, lean_object* v_a_3188_, lean_object* v___x_3189_, lean_object* v_snd_3190_, lean_object* v___x_3191_, lean_object* v___x_3192_, lean_object* v___x_3193_, lean_object* v_alts_3194_, lean_object* v_a_3195_, lean_object* v_zs1_3196_, lean_object* v___ctorRet1_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
uint8_t v___x_15367__boxed_3203_; uint8_t v___x_15368__boxed_3204_; uint8_t v___x_15369__boxed_3205_; lean_object* v_res_3206_; 
v___x_15367__boxed_3203_ = lean_unbox(v___x_3191_);
v___x_15368__boxed_3204_ = lean_unbox(v___x_3192_);
v___x_15369__boxed_3205_ = lean_unbox(v___x_3193_);
v_res_3206_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3187_, v_a_3188_, v___x_3189_, v_snd_3190_, v___x_15367__boxed_3203_, v___x_15368__boxed_3204_, v___x_15369__boxed_3205_, v_alts_3194_, v_a_3195_, v_zs1_3196_, v___ctorRet1_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec_ref(v___ctorRet1_3197_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3207_, lean_object* v_params_3208_, lean_object* v_a_3209_, lean_object* v_snd_3210_, lean_object* v_alts_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_bs_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec_ref(v_alts_3211_);
lean_dec_ref(v_snd_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_tail_3207_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_bs_3214_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; uint8_t v___x_3223_; uint8_t v___x_3224_; lean_object* v_v_3225_; lean_object* v___x_3226_; lean_object* v_bs_x27_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3222_ = l_Lean_instInhabitedExpr;
v___x_3223_ = 0;
v___x_3224_ = 1;
v_v_3225_ = lean_array_uget(v_bs_3214_, v_i_3213_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v_bs_x27_3227_ = lean_array_uset(v_bs_3214_, v_i_3213_, v___x_3226_);
v___x_3228_ = lean_usize_to_nat(v_i_3213_);
lean_inc(v_tail_3207_);
v___x_3229_ = l_Lean_mkConst(v_v_3225_, v_tail_3207_);
v___x_3230_ = l_Lean_mkAppN(v___x_3229_, v_params_3208_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
v___x_3231_ = lean_infer_type(v___x_3230_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc_n(v_a_3232_, 2);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = lean_box(v___x_3220_);
v___x_3234_ = lean_box(v___x_3223_);
v___x_3235_ = lean_box(v___x_3224_);
lean_inc_ref(v_alts_3211_);
lean_inc_ref(v_snd_3210_);
lean_inc_ref(v_a_3209_);
v___f_3236_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3236_, 0, v___x_3222_);
lean_closure_set(v___f_3236_, 1, v_a_3209_);
lean_closure_set(v___f_3236_, 2, v___x_3228_);
lean_closure_set(v___f_3236_, 3, v_snd_3210_);
lean_closure_set(v___f_3236_, 4, v___x_3233_);
lean_closure_set(v___f_3236_, 5, v___x_3234_);
lean_closure_set(v___f_3236_, 6, v___x_3235_);
lean_closure_set(v___f_3236_, 7, v_alts_3211_);
lean_closure_set(v___f_3236_, 8, v_a_3232_);
v___x_3237_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3232_, v___f_3236_, v___x_3223_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = ((size_t)1ULL);
v___x_3240_ = lean_usize_add(v_i_3213_, v___x_3239_);
v___x_3241_ = lean_array_uset(v_bs_x27_3227_, v_i_3213_, v_a_3238_);
v_i_3213_ = v___x_3240_;
v_bs_3214_ = v___x_3241_;
goto _start;
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_bs_x27_3227_);
lean_dec_ref(v_alts_3211_);
lean_dec_ref(v_snd_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_tail_3207_);
v_a_3243_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3237_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3237_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v___x_3228_);
lean_dec_ref(v_bs_x27_3227_);
lean_dec_ref(v_alts_3211_);
lean_dec_ref(v_snd_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_tail_3207_);
v_a_3251_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3231_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3231_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3259_, lean_object* v_params_3260_, lean_object* v_a_3261_, lean_object* v_snd_3262_, lean_object* v_alts_3263_, lean_object* v_sz_3264_, lean_object* v_i_3265_, lean_object* v_bs_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
size_t v_sz_boxed_3272_; size_t v_i_boxed_3273_; lean_object* v_res_3274_; 
v_sz_boxed_3272_ = lean_unbox_usize(v_sz_3264_);
lean_dec(v_sz_3264_);
v_i_boxed_3273_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3259_, v_params_3260_, v_a_3261_, v_snd_3262_, v_alts_3263_, v_sz_boxed_3272_, v_i_boxed_3273_, v_bs_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_params_3260_);
return v_res_3274_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_unsigned_to_nat(16u);
v___x_3277_ = lean_mk_array(v___x_3276_, v___x_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3278_, lean_object* v___x_3279_, uint8_t v___x_3280_, uint8_t v___x_3281_, uint8_t v___x_3282_, lean_object* v_ism1_x27_3283_, lean_object* v_is_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v___x_3288_, lean_object* v_params_3289_, lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v_heq_3292_, lean_object* v_val_3293_, lean_object* v_tail_3294_, lean_object* v_alts_3295_, size_t v_sz_3296_, size_t v___x_3297_, lean_object* v___x_3298_, lean_object* v___x_3299_, lean_object* v_declName_3300_, lean_object* v_levelParams_3301_, lean_object* v_numIndices_3302_, lean_object* v___x_3303_, lean_object* v___x_3304_, lean_object* v_numParams_3305_, lean_object* v_snd_3306_, lean_object* v_ism2_x27_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3314_ = lean_box(v___x_3280_);
v___x_3315_ = lean_box(v___x_3281_);
v___x_3316_ = lean_box(v___x_3282_);
lean_inc_ref(v___x_3285_);
lean_inc_ref_n(v_is_3284_, 2);
lean_inc_ref(v_ism1_x27_3283_);
lean_inc_ref(v_motive_3278_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3317_, 0, v_motive_3278_);
lean_closure_set(v___f_3317_, 1, v___x_3279_);
lean_closure_set(v___f_3317_, 2, v___x_3314_);
lean_closure_set(v___f_3317_, 3, v___x_3315_);
lean_closure_set(v___f_3317_, 4, v___x_3316_);
lean_closure_set(v___f_3317_, 5, v_ism1_x27_3283_);
lean_closure_set(v___f_3317_, 6, v_ism2_x27_3307_);
lean_closure_set(v___f_3317_, 7, v_is_3284_);
lean_closure_set(v___f_3317_, 8, v___x_3285_);
lean_inc_ref(v___x_3286_);
v___x_3318_ = lean_array_push(v_is_3284_, v___x_3286_);
v___x_3319_ = l_Lean_Meta_withNewEqs___redArg(v___x_3318_, v_ism1_x27_3283_, v___f_3317_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3423_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v_fst_3321_ = lean_ctor_get(v_a_3320_, 0);
v_snd_3322_ = lean_ctor_get(v_a_3320_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_a_3320_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3324_ = v_a_3320_;
v_isShared_3325_ = v_isSharedCheck_3423_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_snd_3322_);
lean_inc(v_fst_3321_);
lean_dec(v_a_3320_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3423_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3326_ = l_Lean_mkConst(v___x_3287_, v___x_3288_);
v___x_3327_ = l_Lean_mkAppN(v___x_3326_, v_params_3289_);
v___x_3328_ = l_Lean_Expr_app___override(v___x_3327_, v_fst_3321_);
lean_inc_ref(v_is_3284_);
v___x_3329_ = l_Array_append___redArg(v_is_3284_, v___x_3290_);
v___x_3330_ = l_Array_append___redArg(v___x_3329_, v_is_3284_);
v___x_3331_ = l_Array_append___redArg(v___x_3330_, v___x_3291_);
v___x_3332_ = l_Lean_mkAppN(v___x_3328_, v___x_3331_);
lean_dec_ref(v___x_3331_);
lean_inc_ref(v_heq_3292_);
v___x_3333_ = l_Lean_Expr_app___override(v___x_3332_, v_heq_3292_);
v___x_3334_ = l_Lean_InductiveVal_numCtors(v_val_3293_);
lean_inc_ref(v___x_3333_);
v___x_3335_ = l_Lean_Meta_inferArgumentTypesN(v___x_3334_, v___x_3333_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
lean_inc_ref(v_alts_3295_);
lean_inc(v_snd_3322_);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3294_, v_params_3289_, v_a_3336_, v_snd_3322_, v_alts_3295_, v_sz_3296_, v___x_3297_, v___x_3298_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = l_Lean_mkAppN(v___x_3333_, v_a_3338_);
lean_dec(v_a_3338_);
v___x_3340_ = l_Lean_mkAppN(v___x_3339_, v_snd_3322_);
lean_dec(v_snd_3322_);
lean_inc_ref(v___x_3299_);
v___x_3341_ = lean_array_push(v___x_3299_, v_motive_3278_);
v___x_3342_ = l_Array_append___redArg(v_params_3289_, v___x_3341_);
lean_dec_ref(v___x_3341_);
v___x_3343_ = l_Array_append___redArg(v___x_3342_, v_is_3284_);
lean_dec_ref(v_is_3284_);
v___x_3344_ = lean_unsigned_to_nat(2u);
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3344_);
v___x_3346_ = lean_array_push(v___x_3345_, v___x_3286_);
v___x_3347_ = lean_array_push(v___x_3346_, v___x_3285_);
v___x_3348_ = l_Array_append___redArg(v___x_3343_, v___x_3347_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = lean_array_push(v___x_3299_, v_heq_3292_);
v___x_3350_ = l_Array_append___redArg(v___x_3348_, v___x_3349_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l_Array_append___redArg(v___x_3350_, v_alts_3295_);
lean_dec_ref(v_alts_3295_);
v___x_3352_ = l_Lean_Meta_mkLambdaFVars(v___x_3351_, v___x_3340_, v___x_3280_, v___x_3281_, v___x_3280_, v___x_3281_, v___x_3282_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec_ref(v___x_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_n(v_a_3353_, 2);
lean_dec_ref_known(v___x_3352_, 1);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
v___x_3354_ = lean_infer_type(v_a_3353_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3390_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = lean_box(1);
lean_inc(v_declName_3300_);
v___x_3357_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3300_, v_levelParams_3301_, v_a_3355_, v_a_3353_, v___x_3356_, v___y_3312_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3390_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3390_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3364_ = lean_box(v___x_3280_);
lean_inc_ref(v___x_3363_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3365_, 0, v___x_3363_);
lean_closure_set(v___f_3365_, 1, v___x_3364_);
v___x_3366_ = lean_nat_add(v_numIndices_3302_, v___x_3303_);
lean_inc(v___x_3304_);
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3304_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3303_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3368_);
v___x_3371_ = lean_array_push(v___x_3370_, v___x_3368_);
v___x_3372_ = lean_array_push(v___x_3371_, v___x_3368_);
v___x_3373_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v___x_3373_);
lean_ctor_set(v___x_3324_, 0, v___x_3304_);
v___x_3375_ = v___x_3324_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; uint8_t v___y_3378_; uint8_t v___x_3387_; 
v___x_3376_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3376_, 0, v_numParams_3305_);
lean_ctor_set(v___x_3376_, 1, v___x_3366_);
lean_ctor_set(v___x_3376_, 2, v_snd_3306_);
lean_ctor_set(v___x_3376_, 3, v___x_3367_);
lean_ctor_set(v___x_3376_, 4, v___x_3372_);
lean_ctor_set(v___x_3376_, 5, v___x_3375_);
v___x_3387_ = l_Lean_isPrivateName(v_declName_3300_);
if (v___x_3387_ == 0)
{
v___y_3378_ = v___x_3281_;
goto v___jp_3377_;
}
else
{
v___y_3378_ = v___x_3280_;
goto v___jp_3377_;
}
v___jp_3377_:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3365_, v___y_3378_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref_known(v___x_3379_, 1);
v___x_3380_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3300_);
v___x_3381_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v___x_3380_, v_declName_3300_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref_known(v___x_3381_, 1);
lean_inc_n(v_declName_3300_, 2);
v___x_3382_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3300_, v___x_3376_, v___y_3310_, v___y_3312_);
lean_dec_ref(v___x_3382_);
v___x_3383_ = 0;
v___x_3384_ = l_Lean_Meta_setInlineAttribute(v_declName_3300_, v___x_3383_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3385_; 
lean_dec_ref_known(v___x_3384_, 1);
v___x_3385_ = l_Lean_enableRealizationsForConst(v_declName_3300_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3385_, 1);
v___x_3386_ = l_Lean_compileDecl(v___x_3363_, v___x_3281_, v___y_3311_, v___y_3312_);
return v___x_3386_;
}
else
{
lean_dec_ref(v___x_3363_);
return v___x_3385_;
}
}
else
{
lean_dec_ref(v___x_3363_);
lean_dec(v_declName_3300_);
return v___x_3384_;
}
}
else
{
lean_dec_ref_known(v___x_3376_, 6);
lean_dec_ref(v___x_3363_);
lean_dec(v_declName_3300_);
return v___x_3381_;
}
}
else
{
lean_dec_ref_known(v___x_3376_, 6);
lean_dec_ref(v___x_3363_);
lean_dec(v_declName_3300_);
return v___x_3379_;
}
}
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_a_3353_);
lean_del_object(v___x_3324_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
v_a_3391_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3354_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3354_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_del_object(v___x_3324_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
v_a_3399_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3352_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3352_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___x_3333_);
lean_del_object(v___x_3324_);
lean_dec(v_snd_3322_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_alts_3295_);
lean_dec_ref(v_heq_3292_);
lean_dec_ref(v_params_3289_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_is_3284_);
lean_dec_ref(v_motive_3278_);
v_a_3407_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3337_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3337_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v___x_3333_);
lean_del_object(v___x_3324_);
lean_dec(v_snd_3322_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_alts_3295_);
lean_dec(v_tail_3294_);
lean_dec_ref(v_heq_3292_);
lean_dec_ref(v_params_3289_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_is_3284_);
lean_dec_ref(v_motive_3278_);
v_a_3415_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3335_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3335_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_alts_3295_);
lean_dec(v_tail_3294_);
lean_dec_ref(v_heq_3292_);
lean_dec_ref(v_params_3289_);
lean_dec(v___x_3288_);
lean_dec(v___x_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_is_3284_);
lean_dec_ref(v_motive_3278_);
v_a_3424_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3319_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3319_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3432_ = _args[0];
lean_object* v___x_3433_ = _args[1];
lean_object* v___x_3434_ = _args[2];
lean_object* v___x_3435_ = _args[3];
lean_object* v___x_3436_ = _args[4];
lean_object* v_ism1_x27_3437_ = _args[5];
lean_object* v_is_3438_ = _args[6];
lean_object* v___x_3439_ = _args[7];
lean_object* v___x_3440_ = _args[8];
lean_object* v___x_3441_ = _args[9];
lean_object* v___x_3442_ = _args[10];
lean_object* v_params_3443_ = _args[11];
lean_object* v___x_3444_ = _args[12];
lean_object* v___x_3445_ = _args[13];
lean_object* v_heq_3446_ = _args[14];
lean_object* v_val_3447_ = _args[15];
lean_object* v_tail_3448_ = _args[16];
lean_object* v_alts_3449_ = _args[17];
lean_object* v_sz_3450_ = _args[18];
lean_object* v___x_3451_ = _args[19];
lean_object* v___x_3452_ = _args[20];
lean_object* v___x_3453_ = _args[21];
lean_object* v_declName_3454_ = _args[22];
lean_object* v_levelParams_3455_ = _args[23];
lean_object* v_numIndices_3456_ = _args[24];
lean_object* v___x_3457_ = _args[25];
lean_object* v___x_3458_ = _args[26];
lean_object* v_numParams_3459_ = _args[27];
lean_object* v_snd_3460_ = _args[28];
lean_object* v_ism2_x27_3461_ = _args[29];
lean_object* v_x_3462_ = _args[30];
lean_object* v___y_3463_ = _args[31];
lean_object* v___y_3464_ = _args[32];
lean_object* v___y_3465_ = _args[33];
lean_object* v___y_3466_ = _args[34];
lean_object* v___y_3467_ = _args[35];
_start:
{
uint8_t v___x_15517__boxed_3468_; uint8_t v___x_15518__boxed_3469_; uint8_t v___x_15519__boxed_3470_; size_t v_sz_boxed_3471_; size_t v___x_15528__boxed_3472_; lean_object* v_res_3473_; 
v___x_15517__boxed_3468_ = lean_unbox(v___x_3434_);
v___x_15518__boxed_3469_ = lean_unbox(v___x_3435_);
v___x_15519__boxed_3470_ = lean_unbox(v___x_3436_);
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3450_);
lean_dec(v_sz_3450_);
v___x_15528__boxed_3472_ = lean_unbox_usize(v___x_3451_);
lean_dec(v___x_3451_);
v_res_3473_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3432_, v___x_3433_, v___x_15517__boxed_3468_, v___x_15518__boxed_3469_, v___x_15519__boxed_3470_, v_ism1_x27_3437_, v_is_3438_, v___x_3439_, v___x_3440_, v___x_3441_, v___x_3442_, v_params_3443_, v___x_3444_, v___x_3445_, v_heq_3446_, v_val_3447_, v_tail_3448_, v_alts_3449_, v_sz_boxed_3471_, v___x_15528__boxed_3472_, v___x_3452_, v___x_3453_, v_declName_3454_, v_levelParams_3455_, v_numIndices_3456_, v___x_3457_, v___x_3458_, v_numParams_3459_, v_snd_3460_, v_ism2_x27_3461_, v_x_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v_x_3462_);
lean_dec(v___x_3457_);
lean_dec(v_numIndices_3456_);
lean_dec_ref(v_val_3447_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v___x_3444_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3474_, lean_object* v___x_3475_, uint8_t v___x_3476_, uint8_t v___x_3477_, uint8_t v___x_3478_, lean_object* v_is_3479_, lean_object* v___x_3480_, lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v___x_3483_, lean_object* v_params_3484_, lean_object* v___x_3485_, lean_object* v___x_3486_, lean_object* v_heq_3487_, lean_object* v_val_3488_, lean_object* v_tail_3489_, lean_object* v_alts_3490_, size_t v_sz_3491_, size_t v___x_3492_, lean_object* v___x_3493_, lean_object* v___x_3494_, lean_object* v_declName_3495_, lean_object* v_levelParams_3496_, lean_object* v_numIndices_3497_, lean_object* v___x_3498_, lean_object* v___x_3499_, lean_object* v_numParams_3500_, lean_object* v_snd_3501_, lean_object* v___x_3502_, lean_object* v___x_3503_, lean_object* v_ism1_x27_3504_, lean_object* v_x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
v___x_3511_ = lean_box(v___x_3476_);
v___x_3512_ = lean_box(v___x_3477_);
v___x_3513_ = lean_box(v___x_3478_);
v___x_3514_ = lean_box_usize(v_sz_3491_);
v___x_3515_ = lean_box_usize(v___x_3492_);
v___f_3516_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3516_, 0, v_motive_3474_);
lean_closure_set(v___f_3516_, 1, v___x_3475_);
lean_closure_set(v___f_3516_, 2, v___x_3511_);
lean_closure_set(v___f_3516_, 3, v___x_3512_);
lean_closure_set(v___f_3516_, 4, v___x_3513_);
lean_closure_set(v___f_3516_, 5, v_ism1_x27_3504_);
lean_closure_set(v___f_3516_, 6, v_is_3479_);
lean_closure_set(v___f_3516_, 7, v___x_3480_);
lean_closure_set(v___f_3516_, 8, v___x_3481_);
lean_closure_set(v___f_3516_, 9, v___x_3482_);
lean_closure_set(v___f_3516_, 10, v___x_3483_);
lean_closure_set(v___f_3516_, 11, v_params_3484_);
lean_closure_set(v___f_3516_, 12, v___x_3485_);
lean_closure_set(v___f_3516_, 13, v___x_3486_);
lean_closure_set(v___f_3516_, 14, v_heq_3487_);
lean_closure_set(v___f_3516_, 15, v_val_3488_);
lean_closure_set(v___f_3516_, 16, v_tail_3489_);
lean_closure_set(v___f_3516_, 17, v_alts_3490_);
lean_closure_set(v___f_3516_, 18, v___x_3514_);
lean_closure_set(v___f_3516_, 19, v___x_3515_);
lean_closure_set(v___f_3516_, 20, v___x_3493_);
lean_closure_set(v___f_3516_, 21, v___x_3494_);
lean_closure_set(v___f_3516_, 22, v_declName_3495_);
lean_closure_set(v___f_3516_, 23, v_levelParams_3496_);
lean_closure_set(v___f_3516_, 24, v_numIndices_3497_);
lean_closure_set(v___f_3516_, 25, v___x_3498_);
lean_closure_set(v___f_3516_, 26, v___x_3499_);
lean_closure_set(v___f_3516_, 27, v_numParams_3500_);
lean_closure_set(v___f_3516_, 28, v_snd_3501_);
v___x_3517_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3502_, v___x_3503_, v___f_3516_, v___x_3476_, v___x_3476_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3518_ = _args[0];
lean_object* v___x_3519_ = _args[1];
lean_object* v___x_3520_ = _args[2];
lean_object* v___x_3521_ = _args[3];
lean_object* v___x_3522_ = _args[4];
lean_object* v_is_3523_ = _args[5];
lean_object* v___x_3524_ = _args[6];
lean_object* v___x_3525_ = _args[7];
lean_object* v___x_3526_ = _args[8];
lean_object* v___x_3527_ = _args[9];
lean_object* v_params_3528_ = _args[10];
lean_object* v___x_3529_ = _args[11];
lean_object* v___x_3530_ = _args[12];
lean_object* v_heq_3531_ = _args[13];
lean_object* v_val_3532_ = _args[14];
lean_object* v_tail_3533_ = _args[15];
lean_object* v_alts_3534_ = _args[16];
lean_object* v_sz_3535_ = _args[17];
lean_object* v___x_3536_ = _args[18];
lean_object* v___x_3537_ = _args[19];
lean_object* v___x_3538_ = _args[20];
lean_object* v_declName_3539_ = _args[21];
lean_object* v_levelParams_3540_ = _args[22];
lean_object* v_numIndices_3541_ = _args[23];
lean_object* v___x_3542_ = _args[24];
lean_object* v___x_3543_ = _args[25];
lean_object* v_numParams_3544_ = _args[26];
lean_object* v_snd_3545_ = _args[27];
lean_object* v___x_3546_ = _args[28];
lean_object* v___x_3547_ = _args[29];
lean_object* v_ism1_x27_3548_ = _args[30];
lean_object* v_x_3549_ = _args[31];
lean_object* v___y_3550_ = _args[32];
lean_object* v___y_3551_ = _args[33];
lean_object* v___y_3552_ = _args[34];
lean_object* v___y_3553_ = _args[35];
lean_object* v___y_3554_ = _args[36];
_start:
{
uint8_t v___x_15839__boxed_3555_; uint8_t v___x_15840__boxed_3556_; uint8_t v___x_15841__boxed_3557_; size_t v_sz_boxed_3558_; size_t v___x_15850__boxed_3559_; lean_object* v_res_3560_; 
v___x_15839__boxed_3555_ = lean_unbox(v___x_3520_);
v___x_15840__boxed_3556_ = lean_unbox(v___x_3521_);
v___x_15841__boxed_3557_ = lean_unbox(v___x_3522_);
v_sz_boxed_3558_ = lean_unbox_usize(v_sz_3535_);
lean_dec(v_sz_3535_);
v___x_15850__boxed_3559_ = lean_unbox_usize(v___x_3536_);
lean_dec(v___x_3536_);
v_res_3560_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3518_, v___x_3519_, v___x_15839__boxed_3555_, v___x_15840__boxed_3556_, v___x_15841__boxed_3557_, v_is_3523_, v___x_3524_, v___x_3525_, v___x_3526_, v___x_3527_, v_params_3528_, v___x_3529_, v___x_3530_, v_heq_3531_, v_val_3532_, v_tail_3533_, v_alts_3534_, v_sz_boxed_3558_, v___x_15850__boxed_3559_, v___x_3537_, v___x_3538_, v_declName_3539_, v_levelParams_3540_, v_numIndices_3541_, v___x_3542_, v___x_3543_, v_numParams_3544_, v_snd_3545_, v___x_3546_, v___x_3547_, v_ism1_x27_3548_, v_x_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v_x_3549_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3561_, lean_object* v___x_3562_, lean_object* v_motive_3563_, lean_object* v___x_3564_, uint8_t v___x_3565_, uint8_t v___x_3566_, uint8_t v___x_3567_, lean_object* v_is_3568_, lean_object* v___x_3569_, lean_object* v___x_3570_, lean_object* v___x_3571_, lean_object* v___x_3572_, lean_object* v_params_3573_, lean_object* v___x_3574_, lean_object* v___x_3575_, lean_object* v_heq_3576_, lean_object* v_val_3577_, lean_object* v_tail_3578_, size_t v_sz_3579_, size_t v___x_3580_, lean_object* v___x_3581_, lean_object* v___x_3582_, lean_object* v_declName_3583_, lean_object* v_levelParams_3584_, lean_object* v___x_3585_, lean_object* v___x_3586_, lean_object* v_numParams_3587_, lean_object* v_snd_3588_, lean_object* v___x_3589_, lean_object* v_alts_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; 
v___x_3596_ = lean_nat_add(v_numIndices_3561_, v___x_3562_);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
v___x_3598_ = lean_box(v___x_3565_);
v___x_3599_ = lean_box(v___x_3566_);
v___x_3600_ = lean_box(v___x_3567_);
v___x_3601_ = lean_box_usize(v_sz_3579_);
v___x_3602_ = lean_box_usize(v___x_3580_);
lean_inc_ref(v___x_3597_);
lean_inc_ref(v___x_3589_);
v___f_3603_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3603_, 0, v_motive_3563_);
lean_closure_set(v___f_3603_, 1, v___x_3564_);
lean_closure_set(v___f_3603_, 2, v___x_3598_);
lean_closure_set(v___f_3603_, 3, v___x_3599_);
lean_closure_set(v___f_3603_, 4, v___x_3600_);
lean_closure_set(v___f_3603_, 5, v_is_3568_);
lean_closure_set(v___f_3603_, 6, v___x_3569_);
lean_closure_set(v___f_3603_, 7, v___x_3570_);
lean_closure_set(v___f_3603_, 8, v___x_3571_);
lean_closure_set(v___f_3603_, 9, v___x_3572_);
lean_closure_set(v___f_3603_, 10, v_params_3573_);
lean_closure_set(v___f_3603_, 11, v___x_3574_);
lean_closure_set(v___f_3603_, 12, v___x_3575_);
lean_closure_set(v___f_3603_, 13, v_heq_3576_);
lean_closure_set(v___f_3603_, 14, v_val_3577_);
lean_closure_set(v___f_3603_, 15, v_tail_3578_);
lean_closure_set(v___f_3603_, 16, v_alts_3590_);
lean_closure_set(v___f_3603_, 17, v___x_3601_);
lean_closure_set(v___f_3603_, 18, v___x_3602_);
lean_closure_set(v___f_3603_, 19, v___x_3581_);
lean_closure_set(v___f_3603_, 20, v___x_3582_);
lean_closure_set(v___f_3603_, 21, v_declName_3583_);
lean_closure_set(v___f_3603_, 22, v_levelParams_3584_);
lean_closure_set(v___f_3603_, 23, v_numIndices_3561_);
lean_closure_set(v___f_3603_, 24, v___x_3585_);
lean_closure_set(v___f_3603_, 25, v___x_3586_);
lean_closure_set(v___f_3603_, 26, v_numParams_3587_);
lean_closure_set(v___f_3603_, 27, v_snd_3588_);
lean_closure_set(v___f_3603_, 28, v___x_3589_);
lean_closure_set(v___f_3603_, 29, v___x_3597_);
v___x_3604_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3589_, v___x_3597_, v___f_3603_, v___x_3565_, v___x_3565_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3605_ = _args[0];
lean_object* v___x_3606_ = _args[1];
lean_object* v_motive_3607_ = _args[2];
lean_object* v___x_3608_ = _args[3];
lean_object* v___x_3609_ = _args[4];
lean_object* v___x_3610_ = _args[5];
lean_object* v___x_3611_ = _args[6];
lean_object* v_is_3612_ = _args[7];
lean_object* v___x_3613_ = _args[8];
lean_object* v___x_3614_ = _args[9];
lean_object* v___x_3615_ = _args[10];
lean_object* v___x_3616_ = _args[11];
lean_object* v_params_3617_ = _args[12];
lean_object* v___x_3618_ = _args[13];
lean_object* v___x_3619_ = _args[14];
lean_object* v_heq_3620_ = _args[15];
lean_object* v_val_3621_ = _args[16];
lean_object* v_tail_3622_ = _args[17];
lean_object* v_sz_3623_ = _args[18];
lean_object* v___x_3624_ = _args[19];
lean_object* v___x_3625_ = _args[20];
lean_object* v___x_3626_ = _args[21];
lean_object* v_declName_3627_ = _args[22];
lean_object* v_levelParams_3628_ = _args[23];
lean_object* v___x_3629_ = _args[24];
lean_object* v___x_3630_ = _args[25];
lean_object* v_numParams_3631_ = _args[26];
lean_object* v_snd_3632_ = _args[27];
lean_object* v___x_3633_ = _args[28];
lean_object* v_alts_3634_ = _args[29];
lean_object* v___y_3635_ = _args[30];
lean_object* v___y_3636_ = _args[31];
lean_object* v___y_3637_ = _args[32];
lean_object* v___y_3638_ = _args[33];
lean_object* v___y_3639_ = _args[34];
_start:
{
uint8_t v___x_15932__boxed_3640_; uint8_t v___x_15933__boxed_3641_; uint8_t v___x_15934__boxed_3642_; size_t v_sz_boxed_3643_; size_t v___x_15943__boxed_3644_; lean_object* v_res_3645_; 
v___x_15932__boxed_3640_ = lean_unbox(v___x_3609_);
v___x_15933__boxed_3641_ = lean_unbox(v___x_3610_);
v___x_15934__boxed_3642_ = lean_unbox(v___x_3611_);
v_sz_boxed_3643_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v___x_15943__boxed_3644_ = lean_unbox_usize(v___x_3624_);
lean_dec(v___x_3624_);
v_res_3645_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3605_, v___x_3606_, v_motive_3607_, v___x_3608_, v___x_15932__boxed_3640_, v___x_15933__boxed_3641_, v___x_15934__boxed_3642_, v_is_3612_, v___x_3613_, v___x_3614_, v___x_3615_, v___x_3616_, v_params_3617_, v___x_3618_, v___x_3619_, v_heq_3620_, v_val_3621_, v_tail_3622_, v_sz_boxed_3643_, v___x_15943__boxed_3644_, v___x_3625_, v___x_3626_, v_declName_3627_, v_levelParams_3628_, v___x_3629_, v___x_3630_, v_numParams_3631_, v_snd_3632_, v___x_3633_, v_alts_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___x_3606_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3646_, lean_object* v_declInfos_3647_, lean_object* v_k_3648_, lean_object* v_kind_3649_, lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_kind_boxed_3656_; lean_object* v_res_3657_; 
v_kind_boxed_3656_ = lean_unbox(v_kind_3649_);
v_res_3657_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3646_, v_declInfos_3647_, v_k_3648_, v_kind_boxed_3656_, v_x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3658_, lean_object* v_k_3659_, uint8_t v_kind_3660_, lean_object* v_acc_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; lean_object* v_toApplicative_3668_; lean_object* v_toFunctor_3669_; lean_object* v_toSeq_3670_; lean_object* v_toSeqLeft_3671_; lean_object* v_toSeqRight_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_toApplicative_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3742_; 
v___x_3667_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1);
v_toApplicative_3668_ = lean_ctor_get(v___x_3667_, 0);
v_toFunctor_3669_ = lean_ctor_get(v_toApplicative_3668_, 0);
v_toSeq_3670_ = lean_ctor_get(v_toApplicative_3668_, 2);
v_toSeqLeft_3671_ = lean_ctor_get(v_toApplicative_3668_, 3);
v_toSeqRight_3672_ = lean_ctor_get(v_toApplicative_3668_, 4);
v___f_3673_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2));
v___f_3674_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3));
lean_inc_ref_n(v_toFunctor_3669_, 2);
v___f_3675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3675_, 0, v_toFunctor_3669_);
v___f_3676_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3676_, 0, v_toFunctor_3669_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___f_3675_);
lean_ctor_set(v___x_3677_, 1, v___f_3676_);
lean_inc(v_toSeqRight_3672_);
v___f_3678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3678_, 0, v_toSeqRight_3672_);
lean_inc(v_toSeqLeft_3671_);
v___f_3679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3679_, 0, v_toSeqLeft_3671_);
lean_inc(v_toSeq_3670_);
v___f_3680_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3680_, 0, v_toSeq_3670_);
v___x_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3677_);
lean_ctor_set(v___x_3681_, 1, v___f_3673_);
lean_ctor_set(v___x_3681_, 2, v___f_3680_);
lean_ctor_set(v___x_3681_, 3, v___f_3679_);
lean_ctor_set(v___x_3681_, 4, v___f_3678_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___f_3674_);
v___x_3683_ = l_StateRefT_x27_instMonad___redArg(v___x_3682_);
v_toApplicative_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v___x_3683_, 1);
lean_dec(v_unused_3743_);
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3742_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_toApplicative_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3742_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_toFunctor_3688_; lean_object* v_toSeq_3689_; lean_object* v_toSeqLeft_3690_; lean_object* v_toSeqRight_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3740_; 
v_toFunctor_3688_ = lean_ctor_get(v_toApplicative_3684_, 0);
v_toSeq_3689_ = lean_ctor_get(v_toApplicative_3684_, 2);
v_toSeqLeft_3690_ = lean_ctor_get(v_toApplicative_3684_, 3);
v_toSeqRight_3691_ = lean_ctor_get(v_toApplicative_3684_, 4);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_toApplicative_3684_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v_toApplicative_3684_, 1);
lean_dec(v_unused_3741_);
v___x_3693_ = v_toApplicative_3684_;
v_isShared_3694_ = v_isSharedCheck_3740_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_toSeqRight_3691_);
lean_inc(v_toSeqLeft_3690_);
lean_inc(v_toSeq_3689_);
lean_inc(v_toFunctor_3688_);
lean_dec(v_toApplicative_3684_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3740_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___x_3704_; 
v___f_3695_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4));
v___f_3696_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5));
lean_inc_ref(v_toFunctor_3688_);
v___f_3697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3697_, 0, v_toFunctor_3688_);
v___f_3698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3698_, 0, v_toFunctor_3688_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___f_3697_);
lean_ctor_set(v___x_3699_, 1, v___f_3698_);
v___f_3700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3700_, 0, v_toSeqRight_3691_);
v___f_3701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3701_, 0, v_toSeqLeft_3690_);
v___f_3702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3702_, 0, v_toSeq_3689_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 4, v___f_3700_);
lean_ctor_set(v___x_3693_, 3, v___f_3701_);
lean_ctor_set(v___x_3693_, 2, v___f_3702_);
lean_ctor_set(v___x_3693_, 1, v___f_3695_);
lean_ctor_set(v___x_3693_, 0, v___x_3699_);
v___x_3704_ = v___x_3693_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___f_3695_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v___f_3702_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v___f_3701_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v___f_3700_);
v___x_3704_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___f_3696_);
lean_ctor_set(v___x_3686_, 0, v___x_3704_);
v___x_3706_ = v___x_3686_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___f_3696_);
v___x_3706_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3707_ = lean_array_get_size(v_acc_3661_);
v___x_3708_ = lean_array_get_size(v_declInfos_3658_);
v___x_3709_ = lean_nat_dec_lt(v___x_3707_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3706_);
lean_dec_ref(v_declInfos_3658_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
v___x_3710_ = lean_apply_6(v_k_3659_, v_acc_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___f_3714_; lean_object* v___f_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_snd_3720_; lean_object* v_fst_3721_; lean_object* v_fst_3722_; lean_object* v_snd_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; 
v___x_3711_ = lean_box(0);
v___x_3712_ = 0;
v___x_3713_ = l_Lean_instInhabitedExpr;
v___f_3714_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3714_, 0, v___x_3706_);
lean_closure_set(v___f_3714_, 1, v___x_3713_);
v___f_3715_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3715_, 0, v___f_3714_);
v___x_3716_ = lean_box(v___x_3712_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___f_3715_);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3711_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_array_get(v___x_3718_, v_declInfos_3658_, v___x_3707_);
lean_dec_ref_known(v___x_3718_, 2);
v_snd_3720_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_snd_3720_);
v_fst_3721_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_fst_3721_);
lean_dec(v___x_3719_);
v_fst_3722_ = lean_ctor_get(v_snd_3720_, 0);
lean_inc(v_fst_3722_);
v_snd_3723_ = lean_ctor_get(v_snd_3720_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_snd_3720_);
v___x_3724_ = lean_box(v_kind_3660_);
lean_inc_ref(v_acc_3661_);
v___f_3725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3725_, 0, v_acc_3661_);
lean_closure_set(v___f_3725_, 1, v_declInfos_3658_);
lean_closure_set(v___f_3725_, 2, v_k_3659_);
lean_closure_set(v___f_3725_, 3, v___x_3724_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
v___x_3726_ = lean_apply_6(v_snd_3723_, v_acc_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v___x_3728_ = lean_unbox(v_fst_3722_);
lean_dec(v_fst_3722_);
v___x_3729_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3721_, v___x_3728_, v_a_3727_, v___f_3725_, v_kind_3660_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3729_;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___f_3725_);
lean_dec(v_fst_3722_);
lean_dec(v_fst_3721_);
v_a_3730_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3726_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3726_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3744_, lean_object* v_declInfos_3745_, lean_object* v_k_3746_, uint8_t v_kind_3747_, lean_object* v_x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_array_push(v_acc_3744_, v_x_3748_);
v___x_3755_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3745_, v_k_3746_, v_kind_3747_, v___x_3754_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3756_, lean_object* v_k_3757_, lean_object* v_kind_3758_, lean_object* v_acc_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v_kind_boxed_3765_; lean_object* v_res_3766_; 
v_kind_boxed_3765_ = lean_unbox(v_kind_3758_);
v_res_3766_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3756_, v_k_3757_, v_kind_boxed_3765_, v_acc_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3767_, lean_object* v_k_3768_, uint8_t v_kind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0));
v___x_3776_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3767_, v_k_3768_, v_kind_3769_, v___x_3775_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3777_, lean_object* v_k_3778_, lean_object* v_kind_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
uint8_t v_kind_boxed_3785_; lean_object* v_res_3786_; 
v_kind_boxed_3785_ = lean_unbox(v_kind_3779_);
v_res_3786_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3777_, v_k_3778_, v_kind_boxed_3785_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3787_, lean_object* v_k_3788_, uint8_t v_kind_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
size_t v_sz_3795_; size_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_sz_3795_ = lean_array_size(v_declInfos_3787_);
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_3795_, v___x_3796_, v_declInfos_3787_);
v___x_3798_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3797_, v_k_3788_, v_kind_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3799_, lean_object* v_k_3800_, lean_object* v_kind_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
uint8_t v_kind_boxed_3807_; lean_object* v_res_3808_; 
v_kind_boxed_3807_ = lean_unbox(v_kind_3801_);
v_res_3808_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3799_, v_k_3800_, v_kind_boxed_3807_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3809_, lean_object* v_k_3810_, uint8_t v_kind_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
size_t v_sz_3817_; size_t v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_sz_3817_ = lean_array_size(v_declInfos_3809_);
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3817_, v___x_3818_, v_declInfos_3809_);
v___x_3820_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3819_, v_k_3810_, v_kind_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3821_, lean_object* v_k_3822_, lean_object* v_kind_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v_kind_boxed_3829_; lean_object* v_res_3830_; 
v_kind_boxed_3829_ = lean_unbox(v_kind_3823_);
v_res_3830_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3821_, v_k_3822_, v_kind_boxed_3829_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3830_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3833_ = lean_box(0);
v___x_3834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3835_ = l_Lean_mkConst(v___x_3834_, v___x_3833_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3836_, lean_object* v_v_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v_motive_3841_, uint8_t v___x_3842_, uint8_t v___x_3843_, uint8_t v___x_3844_, lean_object* v_zs12_3845_, lean_object* v_is_3846_, lean_object* v_fields1_3847_, lean_object* v_fields2_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v_e_3864_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_inc_ref(v___x_3840_);
v___x_3874_ = l_Lean_mkAppN(v___x_3840_, v_fields1_3847_);
v___x_3875_ = l_Lean_mkAppN(v___x_3840_, v_fields2_3848_);
lean_inc(v___x_3838_);
v___x_3876_ = l_Lean_mkNatLit(v___x_3838_);
v___x_3877_ = l_Lean_Meta_mkEqRefl(v___x_3876_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = lean_unsigned_to_nat(3u);
v___x_3880_ = lean_mk_empty_array_with_capacity(v___x_3879_);
v___x_3881_ = lean_array_push(v___x_3880_, v___x_3874_);
v___x_3882_ = lean_array_push(v___x_3881_, v___x_3875_);
v___x_3883_ = lean_array_push(v___x_3882_, v_a_3878_);
v___x_3884_ = l_Array_append___redArg(v_is_3846_, v___x_3883_);
lean_dec_ref(v___x_3883_);
v___x_3885_ = l_Lean_mkAppN(v_motive_3841_, v___x_3884_);
lean_dec_ref(v___x_3884_);
v___x_3886_ = l_Lean_Meta_mkForallFVars(v_zs12_3845_, v___x_3885_, v___x_3842_, v___x_3843_, v___x_3843_, v___x_3844_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_array_get_size(v_zs12_3845_);
v___x_3889_ = lean_nat_dec_eq(v___x_3888_, v___x_3836_);
if (v___x_3889_ == 0)
{
v_e_3864_ = v_a_3887_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3891_ = l_Lean_mkArrow(v___x_3890_, v_a_3887_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_e_3864_ = v_a_3892_;
goto v___jp_3863_;
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v___x_3838_);
lean_dec(v_v_3837_);
lean_dec(v___x_3836_);
v_a_3893_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3891_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3891_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v___x_3838_);
lean_dec(v_v_3837_);
lean_dec(v___x_3836_);
v_a_3901_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3886_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3886_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v___x_3874_);
lean_dec_ref(v_is_3846_);
lean_dec_ref(v_motive_3841_);
lean_dec(v___x_3838_);
lean_dec(v_v_3837_);
lean_dec(v___x_3836_);
v_a_3909_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3877_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3877_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
v___jp_3854_:
{
lean_object* v___x_3857_; uint8_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3857_ = lean_array_get_size(v_zs12_3845_);
v___x_3858_ = lean_nat_dec_eq(v___x_3857_, v___x_3836_);
v___x_3859_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3836_);
lean_ctor_set_uint8(v___x_3859_, sizeof(void*)*2, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___y_3856_);
lean_ctor_set(v___x_3860_, 1, v___y_3855_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3859_);
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
v___jp_3863_:
{
if (lean_obj_tag(v_v_3837_) == 1)
{
lean_object* v_str_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec(v___x_3838_);
v_str_3865_ = lean_ctor_get(v_v_3837_, 1);
lean_inc_ref(v_str_3865_);
lean_dec_ref_known(v_v_3837_, 2);
v___x_3866_ = lean_box(0);
v___x_3867_ = l_Lean_Name_str___override(v___x_3866_, v_str_3865_);
v___y_3855_ = v_e_3864_;
v___y_3856_ = v___x_3867_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_dec(v_v_3837_);
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3869_ = lean_nat_add(v___x_3838_, v___x_3839_);
lean_dec(v___x_3838_);
v___x_3870_ = l_Nat_reprFast(v___x_3869_);
v___x_3871_ = lean_string_append(v___x_3868_, v___x_3870_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = lean_box(0);
v___x_3873_ = l_Lean_Name_str___override(v___x_3872_, v___x_3871_);
v___y_3855_ = v_e_3864_;
v___y_3856_ = v___x_3873_;
goto v___jp_3854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3917_ = _args[0];
lean_object* v_v_3918_ = _args[1];
lean_object* v___x_3919_ = _args[2];
lean_object* v___x_3920_ = _args[3];
lean_object* v___x_3921_ = _args[4];
lean_object* v_motive_3922_ = _args[5];
lean_object* v___x_3923_ = _args[6];
lean_object* v___x_3924_ = _args[7];
lean_object* v___x_3925_ = _args[8];
lean_object* v_zs12_3926_ = _args[9];
lean_object* v_is_3927_ = _args[10];
lean_object* v_fields1_3928_ = _args[11];
lean_object* v_fields2_3929_ = _args[12];
lean_object* v___y_3930_ = _args[13];
lean_object* v___y_3931_ = _args[14];
lean_object* v___y_3932_ = _args[15];
lean_object* v___y_3933_ = _args[16];
lean_object* v___y_3934_ = _args[17];
_start:
{
uint8_t v___x_16279__boxed_3935_; uint8_t v___x_16280__boxed_3936_; uint8_t v___x_16281__boxed_3937_; lean_object* v_res_3938_; 
v___x_16279__boxed_3935_ = lean_unbox(v___x_3923_);
v___x_16280__boxed_3936_ = lean_unbox(v___x_3924_);
v___x_16281__boxed_3937_ = lean_unbox(v___x_3925_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3917_, v_v_3918_, v___x_3919_, v___x_3920_, v___x_3921_, v_motive_3922_, v___x_16279__boxed_3935_, v___x_16280__boxed_3936_, v___x_16281__boxed_3937_, v_zs12_3926_, v_is_3927_, v_fields1_3928_, v_fields2_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec_ref(v_fields2_3929_);
lean_dec_ref(v_fields1_3928_);
lean_dec_ref(v_zs12_3926_);
lean_dec(v___x_3920_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3939_, lean_object* v_params_3940_, lean_object* v_motive_3941_, size_t v_sz_3942_, size_t v_i_3943_, lean_object* v_bs_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v___x_3950_; 
v___x_3950_ = lean_usize_dec_lt(v_i_3943_, v_sz_3942_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec_ref(v_motive_3941_);
lean_dec(v_tail_3939_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_bs_3944_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; uint8_t v___x_3955_; lean_object* v_v_3956_; lean_object* v_bs_x27_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___f_3964_; lean_object* v___x_3965_; 
v___x_3952_ = lean_unsigned_to_nat(0u);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = 0;
v___x_3955_ = 1;
v_v_3956_ = lean_array_uget(v_bs_3944_, v_i_3943_);
v_bs_x27_3957_ = lean_array_uset(v_bs_3944_, v_i_3943_, v___x_3952_);
v___x_3958_ = lean_usize_to_nat(v_i_3943_);
lean_inc(v_tail_3939_);
lean_inc(v_v_3956_);
v___x_3959_ = l_Lean_mkConst(v_v_3956_, v_tail_3939_);
v___x_3960_ = l_Lean_mkAppN(v___x_3959_, v_params_3940_);
v___x_3961_ = lean_box(v___x_3954_);
v___x_3962_ = lean_box(v___x_3950_);
v___x_3963_ = lean_box(v___x_3955_);
lean_inc_ref(v_motive_3941_);
lean_inc_ref(v___x_3960_);
v___f_3964_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3964_, 0, v___x_3952_);
lean_closure_set(v___f_3964_, 1, v_v_3956_);
lean_closure_set(v___f_3964_, 2, v___x_3958_);
lean_closure_set(v___f_3964_, 3, v___x_3953_);
lean_closure_set(v___f_3964_, 4, v___x_3960_);
lean_closure_set(v___f_3964_, 5, v_motive_3941_);
lean_closure_set(v___f_3964_, 6, v___x_3961_);
lean_closure_set(v___f_3964_, 7, v___x_3962_);
lean_closure_set(v___f_3964_, 8, v___x_3963_);
v___x_3965_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3960_, v___f_3964_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = ((size_t)1ULL);
v___x_3968_ = lean_usize_add(v_i_3943_, v___x_3967_);
v___x_3969_ = lean_array_uset(v_bs_x27_3957_, v_i_3943_, v_a_3966_);
v_i_3943_ = v___x_3968_;
v_bs_3944_ = v___x_3969_;
goto _start;
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v_bs_x27_3957_);
lean_dec_ref(v_motive_3941_);
lean_dec(v_tail_3939_);
v_a_3971_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3965_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3965_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3979_, lean_object* v_params_3980_, lean_object* v_motive_3981_, lean_object* v_sz_3982_, lean_object* v_i_3983_, lean_object* v_bs_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
size_t v_sz_boxed_3990_; size_t v_i_boxed_3991_; lean_object* v_res_3992_; 
v_sz_boxed_3990_ = lean_unbox_usize(v_sz_3982_);
lean_dec(v_sz_3982_);
v_i_boxed_3991_ = lean_unbox_usize(v_i_3983_);
lean_dec(v_i_3983_);
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3979_, v_params_3980_, v_motive_3981_, v_sz_boxed_3990_, v_i_boxed_3991_, v_bs_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec_ref(v_params_3980_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3995_, lean_object* v_tail_3996_, lean_object* v_params_3997_, lean_object* v_numIndices_3998_, lean_object* v___x_3999_, lean_object* v___x_4000_, uint8_t v___x_4001_, uint8_t v___x_4002_, uint8_t v___x_4003_, lean_object* v_is_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, lean_object* v___x_4007_, lean_object* v___x_4008_, lean_object* v___x_4009_, lean_object* v___x_4010_, lean_object* v_heq_4011_, lean_object* v_val_4012_, lean_object* v___x_4013_, lean_object* v_declName_4014_, lean_object* v_levelParams_4015_, lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v_numParams_4018_, lean_object* v___x_4019_, lean_object* v_motive_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; size_t v_sz_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v___x_4026_ = lean_array_mk(v_ctors_3995_);
v_sz_4027_ = lean_array_size(v___x_4026_);
v___x_4028_ = ((size_t)0ULL);
lean_inc_ref(v___x_4026_);
lean_inc_ref(v_motive_4020_);
lean_inc(v_tail_3996_);
v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3996_, v_params_3997_, v_motive_4020_, v_sz_4027_, v___x_4028_, v___x_4026_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; lean_object* v_fst_4032_; lean_object* v_snd_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___f_4039_; uint8_t v___x_4040_; lean_object* v___x_4041_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = l_Array_unzip___redArg(v_a_4030_);
lean_dec(v_a_4030_);
v_fst_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_fst_4032_);
v_snd_4033_ = lean_ctor_get(v___x_4031_, 1);
lean_inc(v_snd_4033_);
lean_dec_ref(v___x_4031_);
v___x_4034_ = lean_box(v___x_4001_);
v___x_4035_ = lean_box(v___x_4002_);
v___x_4036_ = lean_box(v___x_4003_);
v___x_4037_ = lean_box_usize(v_sz_4027_);
v___x_4038_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4039_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4039_, 0, v_numIndices_3998_);
lean_closure_set(v___f_4039_, 1, v___x_3999_);
lean_closure_set(v___f_4039_, 2, v_motive_4020_);
lean_closure_set(v___f_4039_, 3, v___x_4000_);
lean_closure_set(v___f_4039_, 4, v___x_4034_);
lean_closure_set(v___f_4039_, 5, v___x_4035_);
lean_closure_set(v___f_4039_, 6, v___x_4036_);
lean_closure_set(v___f_4039_, 7, v_is_4004_);
lean_closure_set(v___f_4039_, 8, v___x_4005_);
lean_closure_set(v___f_4039_, 9, v___x_4006_);
lean_closure_set(v___f_4039_, 10, v___x_4007_);
lean_closure_set(v___f_4039_, 11, v___x_4008_);
lean_closure_set(v___f_4039_, 12, v_params_3997_);
lean_closure_set(v___f_4039_, 13, v___x_4009_);
lean_closure_set(v___f_4039_, 14, v___x_4010_);
lean_closure_set(v___f_4039_, 15, v_heq_4011_);
lean_closure_set(v___f_4039_, 16, v_val_4012_);
lean_closure_set(v___f_4039_, 17, v_tail_3996_);
lean_closure_set(v___f_4039_, 18, v___x_4037_);
lean_closure_set(v___f_4039_, 19, v___x_4038_);
lean_closure_set(v___f_4039_, 20, v___x_4026_);
lean_closure_set(v___f_4039_, 21, v___x_4013_);
lean_closure_set(v___f_4039_, 22, v_declName_4014_);
lean_closure_set(v___f_4039_, 23, v_levelParams_4015_);
lean_closure_set(v___f_4039_, 24, v___x_4016_);
lean_closure_set(v___f_4039_, 25, v___x_4017_);
lean_closure_set(v___f_4039_, 26, v_numParams_4018_);
lean_closure_set(v___f_4039_, 27, v_snd_4033_);
lean_closure_set(v___f_4039_, 28, v___x_4019_);
v___x_4040_ = 0;
v___x_4041_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4032_, v___f_4039_, v___x_4040_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec_ref(v___x_4026_);
lean_dec_ref(v_motive_4020_);
lean_dec_ref(v___x_4019_);
lean_dec(v_numParams_4018_);
lean_dec(v___x_4017_);
lean_dec(v___x_4016_);
lean_dec(v_levelParams_4015_);
lean_dec(v_declName_4014_);
lean_dec_ref(v___x_4013_);
lean_dec_ref(v_val_4012_);
lean_dec_ref(v_heq_4011_);
lean_dec_ref(v___x_4010_);
lean_dec_ref(v___x_4009_);
lean_dec(v___x_4008_);
lean_dec(v___x_4007_);
lean_dec_ref(v___x_4006_);
lean_dec_ref(v___x_4005_);
lean_dec_ref(v_is_4004_);
lean_dec_ref(v___x_4000_);
lean_dec(v___x_3999_);
lean_dec(v_numIndices_3998_);
lean_dec_ref(v_params_3997_);
lean_dec(v_tail_3996_);
v_a_4042_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4029_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4029_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4050_ = _args[0];
lean_object* v_tail_4051_ = _args[1];
lean_object* v_params_4052_ = _args[2];
lean_object* v_numIndices_4053_ = _args[3];
lean_object* v___x_4054_ = _args[4];
lean_object* v___x_4055_ = _args[5];
lean_object* v___x_4056_ = _args[6];
lean_object* v___x_4057_ = _args[7];
lean_object* v___x_4058_ = _args[8];
lean_object* v_is_4059_ = _args[9];
lean_object* v___x_4060_ = _args[10];
lean_object* v___x_4061_ = _args[11];
lean_object* v___x_4062_ = _args[12];
lean_object* v___x_4063_ = _args[13];
lean_object* v___x_4064_ = _args[14];
lean_object* v___x_4065_ = _args[15];
lean_object* v_heq_4066_ = _args[16];
lean_object* v_val_4067_ = _args[17];
lean_object* v___x_4068_ = _args[18];
lean_object* v_declName_4069_ = _args[19];
lean_object* v_levelParams_4070_ = _args[20];
lean_object* v___x_4071_ = _args[21];
lean_object* v___x_4072_ = _args[22];
lean_object* v_numParams_4073_ = _args[23];
lean_object* v___x_4074_ = _args[24];
lean_object* v_motive_4075_ = _args[25];
lean_object* v___y_4076_ = _args[26];
lean_object* v___y_4077_ = _args[27];
lean_object* v___y_4078_ = _args[28];
lean_object* v___y_4079_ = _args[29];
lean_object* v___y_4080_ = _args[30];
_start:
{
uint8_t v___x_16516__boxed_4081_; uint8_t v___x_16517__boxed_4082_; uint8_t v___x_16518__boxed_4083_; lean_object* v_res_4084_; 
v___x_16516__boxed_4081_ = lean_unbox(v___x_4056_);
v___x_16517__boxed_4082_ = lean_unbox(v___x_4057_);
v___x_16518__boxed_4083_ = lean_unbox(v___x_4058_);
v_res_4084_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4050_, v_tail_4051_, v_params_4052_, v_numIndices_4053_, v___x_4054_, v___x_4055_, v___x_16516__boxed_4081_, v___x_16517__boxed_4082_, v___x_16518__boxed_4083_, v_is_4059_, v___x_4060_, v___x_4061_, v___x_4062_, v___x_4063_, v___x_4064_, v___x_4065_, v_heq_4066_, v_val_4067_, v___x_4068_, v_declName_4069_, v_levelParams_4070_, v___x_4071_, v___x_4072_, v_numParams_4073_, v___x_4074_, v_motive_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4085_, lean_object* v___x_4086_, lean_object* v_is_4087_, lean_object* v_head_4088_, lean_object* v_ctors_4089_, lean_object* v_tail_4090_, lean_object* v_params_4091_, lean_object* v_numIndices_4092_, lean_object* v___x_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v_val_4098_, lean_object* v___x_4099_, lean_object* v_declName_4100_, lean_object* v_levelParams_4101_, lean_object* v___x_4102_, lean_object* v_numParams_4103_, lean_object* v___x_4104_, lean_object* v_heq_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; uint8_t v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___f_4124_; lean_object* v___x_4125_; 
v___x_4111_ = lean_unsigned_to_nat(3u);
v___x_4112_ = lean_mk_empty_array_with_capacity(v___x_4111_);
lean_inc_ref(v___x_4085_);
v___x_4113_ = lean_array_push(v___x_4112_, v___x_4085_);
lean_inc_ref(v___x_4086_);
v___x_4114_ = lean_array_push(v___x_4113_, v___x_4086_);
lean_inc_ref(v_heq_4105_);
v___x_4115_ = lean_array_push(v___x_4114_, v_heq_4105_);
lean_inc_ref(v_is_4087_);
v___x_4116_ = l_Array_append___redArg(v_is_4087_, v___x_4115_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = l_Lean_mkSort(v_head_4088_);
v___x_4118_ = 0;
v___x_4119_ = 1;
v___x_4120_ = 1;
v___x_4121_ = lean_box(v___x_4118_);
v___x_4122_ = lean_box(v___x_4119_);
v___x_4123_ = lean_box(v___x_4120_);
lean_inc_ref(v___x_4116_);
v___f_4124_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4124_, 0, v_ctors_4089_);
lean_closure_set(v___f_4124_, 1, v_tail_4090_);
lean_closure_set(v___f_4124_, 2, v_params_4091_);
lean_closure_set(v___f_4124_, 3, v_numIndices_4092_);
lean_closure_set(v___f_4124_, 4, v___x_4093_);
lean_closure_set(v___f_4124_, 5, v___x_4116_);
lean_closure_set(v___f_4124_, 6, v___x_4121_);
lean_closure_set(v___f_4124_, 7, v___x_4122_);
lean_closure_set(v___f_4124_, 8, v___x_4123_);
lean_closure_set(v___f_4124_, 9, v_is_4087_);
lean_closure_set(v___f_4124_, 10, v___x_4086_);
lean_closure_set(v___f_4124_, 11, v___x_4085_);
lean_closure_set(v___f_4124_, 12, v___x_4094_);
lean_closure_set(v___f_4124_, 13, v___x_4095_);
lean_closure_set(v___f_4124_, 14, v___x_4096_);
lean_closure_set(v___f_4124_, 15, v___x_4097_);
lean_closure_set(v___f_4124_, 16, v_heq_4105_);
lean_closure_set(v___f_4124_, 17, v_val_4098_);
lean_closure_set(v___f_4124_, 18, v___x_4099_);
lean_closure_set(v___f_4124_, 19, v_declName_4100_);
lean_closure_set(v___f_4124_, 20, v_levelParams_4101_);
lean_closure_set(v___f_4124_, 21, v___x_4111_);
lean_closure_set(v___f_4124_, 22, v___x_4102_);
lean_closure_set(v___f_4124_, 23, v_numParams_4103_);
lean_closure_set(v___f_4124_, 24, v___x_4104_);
v___x_4125_ = l_Lean_Meta_mkForallFVars(v___x_4116_, v___x_4117_, v___x_4118_, v___x_4119_, v___x_4119_, v___x_4120_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec_ref(v___x_4116_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4127_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4128_ = 0;
v___x_4129_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4127_, v___x_4120_, v_a_4126_, v___f_4124_, v___x_4128_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___f_4124_);
v_a_4130_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4125_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4125_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4138_ = _args[0];
lean_object* v___x_4139_ = _args[1];
lean_object* v_is_4140_ = _args[2];
lean_object* v_head_4141_ = _args[3];
lean_object* v_ctors_4142_ = _args[4];
lean_object* v_tail_4143_ = _args[5];
lean_object* v_params_4144_ = _args[6];
lean_object* v_numIndices_4145_ = _args[7];
lean_object* v___x_4146_ = _args[8];
lean_object* v___x_4147_ = _args[9];
lean_object* v___x_4148_ = _args[10];
lean_object* v___x_4149_ = _args[11];
lean_object* v___x_4150_ = _args[12];
lean_object* v_val_4151_ = _args[13];
lean_object* v___x_4152_ = _args[14];
lean_object* v_declName_4153_ = _args[15];
lean_object* v_levelParams_4154_ = _args[16];
lean_object* v___x_4155_ = _args[17];
lean_object* v_numParams_4156_ = _args[18];
lean_object* v___x_4157_ = _args[19];
lean_object* v_heq_4158_ = _args[20];
lean_object* v___y_4159_ = _args[21];
lean_object* v___y_4160_ = _args[22];
lean_object* v___y_4161_ = _args[23];
lean_object* v___y_4162_ = _args[24];
lean_object* v___y_4163_ = _args[25];
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4138_, v___x_4139_, v_is_4140_, v_head_4141_, v_ctors_4142_, v_tail_4143_, v_params_4144_, v_numIndices_4145_, v___x_4146_, v___x_4147_, v___x_4148_, v___x_4149_, v___x_4150_, v_val_4151_, v___x_4152_, v_declName_4153_, v_levelParams_4154_, v___x_4155_, v_numParams_4156_, v___x_4157_, v_heq_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4165_, lean_object* v_x1_4166_, lean_object* v_indName_4167_, lean_object* v_tail_4168_, lean_object* v_params_4169_, lean_object* v_is_4170_, lean_object* v___x_4171_, lean_object* v_head_4172_, lean_object* v_ctors_4173_, lean_object* v_numIndices_4174_, lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v_val_4177_, lean_object* v_declName_4178_, lean_object* v_levelParams_4179_, lean_object* v_numParams_4180_, lean_object* v___x_4181_, lean_object* v_x2_4182_, lean_object* v_x_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = lean_array_get_borrowed(v___x_4165_, v_x1_4166_, v___x_4189_);
v___x_4191_ = lean_array_get_borrowed(v___x_4165_, v_x2_4182_, v___x_4189_);
v___x_4192_ = l_Lean_mkCtorIdxName(v_indName_4167_);
lean_inc(v_tail_4168_);
v___x_4193_ = l_Lean_mkConst(v___x_4192_, v_tail_4168_);
lean_inc_ref(v_params_4169_);
v___x_4194_ = l_Array_append___redArg(v_params_4169_, v_is_4170_);
v___x_4195_ = lean_mk_empty_array_with_capacity(v___x_4171_);
lean_inc_n(v___x_4190_, 2);
lean_inc_ref_n(v___x_4195_, 2);
v___x_4196_ = lean_array_push(v___x_4195_, v___x_4190_);
lean_inc_ref(v___x_4194_);
v___x_4197_ = l_Array_append___redArg(v___x_4194_, v___x_4196_);
lean_inc_ref(v___x_4193_);
v___x_4198_ = l_Lean_mkAppN(v___x_4193_, v___x_4197_);
lean_dec_ref(v___x_4197_);
lean_inc_n(v___x_4191_, 2);
v___x_4199_ = lean_array_push(v___x_4195_, v___x_4191_);
lean_inc_ref(v___x_4199_);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4200_, 0, v___x_4190_);
lean_closure_set(v___f_4200_, 1, v___x_4191_);
lean_closure_set(v___f_4200_, 2, v_is_4170_);
lean_closure_set(v___f_4200_, 3, v_head_4172_);
lean_closure_set(v___f_4200_, 4, v_ctors_4173_);
lean_closure_set(v___f_4200_, 5, v_tail_4168_);
lean_closure_set(v___f_4200_, 6, v_params_4169_);
lean_closure_set(v___f_4200_, 7, v_numIndices_4174_);
lean_closure_set(v___f_4200_, 8, v___x_4171_);
lean_closure_set(v___f_4200_, 9, v___x_4175_);
lean_closure_set(v___f_4200_, 10, v___x_4176_);
lean_closure_set(v___f_4200_, 11, v___x_4196_);
lean_closure_set(v___f_4200_, 12, v___x_4199_);
lean_closure_set(v___f_4200_, 13, v_val_4177_);
lean_closure_set(v___f_4200_, 14, v___x_4195_);
lean_closure_set(v___f_4200_, 15, v_declName_4178_);
lean_closure_set(v___f_4200_, 16, v_levelParams_4179_);
lean_closure_set(v___f_4200_, 17, v___x_4189_);
lean_closure_set(v___f_4200_, 18, v_numParams_4180_);
lean_closure_set(v___f_4200_, 19, v___x_4181_);
v___x_4201_ = l_Array_append___redArg(v___x_4194_, v___x_4199_);
lean_dec_ref(v___x_4199_);
v___x_4202_ = l_Lean_mkAppN(v___x_4193_, v___x_4201_);
lean_dec_ref(v___x_4201_);
v___x_4203_ = l_Lean_Meta_mkEq(v___x_4198_, v___x_4202_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4205_, v_a_4204_, v___f_4200_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v___f_4200_);
v_a_4207_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4203_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4203_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4215_ = _args[0];
lean_object* v_x1_4216_ = _args[1];
lean_object* v_indName_4217_ = _args[2];
lean_object* v_tail_4218_ = _args[3];
lean_object* v_params_4219_ = _args[4];
lean_object* v_is_4220_ = _args[5];
lean_object* v___x_4221_ = _args[6];
lean_object* v_head_4222_ = _args[7];
lean_object* v_ctors_4223_ = _args[8];
lean_object* v_numIndices_4224_ = _args[9];
lean_object* v___x_4225_ = _args[10];
lean_object* v___x_4226_ = _args[11];
lean_object* v_val_4227_ = _args[12];
lean_object* v_declName_4228_ = _args[13];
lean_object* v_levelParams_4229_ = _args[14];
lean_object* v_numParams_4230_ = _args[15];
lean_object* v___x_4231_ = _args[16];
lean_object* v_x2_4232_ = _args[17];
lean_object* v_x_4233_ = _args[18];
lean_object* v___y_4234_ = _args[19];
lean_object* v___y_4235_ = _args[20];
lean_object* v___y_4236_ = _args[21];
lean_object* v___y_4237_ = _args[22];
lean_object* v___y_4238_ = _args[23];
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4215_, v_x1_4216_, v_indName_4217_, v_tail_4218_, v_params_4219_, v_is_4220_, v___x_4221_, v_head_4222_, v_ctors_4223_, v_numIndices_4224_, v___x_4225_, v___x_4226_, v_val_4227_, v_declName_4228_, v_levelParams_4229_, v_numParams_4230_, v___x_4231_, v_x2_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec_ref(v_x_4233_);
lean_dec_ref(v_x2_4232_);
lean_dec_ref(v_x1_4216_);
lean_dec_ref(v___x_4215_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4240_, lean_object* v_indName_4241_, lean_object* v_tail_4242_, lean_object* v_params_4243_, lean_object* v_is_4244_, lean_object* v___x_4245_, lean_object* v_head_4246_, lean_object* v_ctors_4247_, lean_object* v_numIndices_4248_, lean_object* v___x_4249_, lean_object* v___x_4250_, lean_object* v_val_4251_, lean_object* v_declName_4252_, lean_object* v_levelParams_4253_, lean_object* v_numParams_4254_, lean_object* v___x_4255_, lean_object* v_t_4256_, lean_object* v___x_4257_, lean_object* v_x1_4258_, lean_object* v_x_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___f_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; 
v___f_4265_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4265_, 0, v___x_4240_);
lean_closure_set(v___f_4265_, 1, v_x1_4258_);
lean_closure_set(v___f_4265_, 2, v_indName_4241_);
lean_closure_set(v___f_4265_, 3, v_tail_4242_);
lean_closure_set(v___f_4265_, 4, v_params_4243_);
lean_closure_set(v___f_4265_, 5, v_is_4244_);
lean_closure_set(v___f_4265_, 6, v___x_4245_);
lean_closure_set(v___f_4265_, 7, v_head_4246_);
lean_closure_set(v___f_4265_, 8, v_ctors_4247_);
lean_closure_set(v___f_4265_, 9, v_numIndices_4248_);
lean_closure_set(v___f_4265_, 10, v___x_4249_);
lean_closure_set(v___f_4265_, 11, v___x_4250_);
lean_closure_set(v___f_4265_, 12, v_val_4251_);
lean_closure_set(v___f_4265_, 13, v_declName_4252_);
lean_closure_set(v___f_4265_, 14, v_levelParams_4253_);
lean_closure_set(v___f_4265_, 15, v_numParams_4254_);
lean_closure_set(v___f_4265_, 16, v___x_4255_);
v___x_4266_ = 0;
v___x_4267_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4256_, v___x_4257_, v___f_4265_, v___x_4266_, v___x_4266_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4268_ = _args[0];
lean_object* v_indName_4269_ = _args[1];
lean_object* v_tail_4270_ = _args[2];
lean_object* v_params_4271_ = _args[3];
lean_object* v_is_4272_ = _args[4];
lean_object* v___x_4273_ = _args[5];
lean_object* v_head_4274_ = _args[6];
lean_object* v_ctors_4275_ = _args[7];
lean_object* v_numIndices_4276_ = _args[8];
lean_object* v___x_4277_ = _args[9];
lean_object* v___x_4278_ = _args[10];
lean_object* v_val_4279_ = _args[11];
lean_object* v_declName_4280_ = _args[12];
lean_object* v_levelParams_4281_ = _args[13];
lean_object* v_numParams_4282_ = _args[14];
lean_object* v___x_4283_ = _args[15];
lean_object* v_t_4284_ = _args[16];
lean_object* v___x_4285_ = _args[17];
lean_object* v_x1_4286_ = _args[18];
lean_object* v_x_4287_ = _args[19];
lean_object* v___y_4288_ = _args[20];
lean_object* v___y_4289_ = _args[21];
lean_object* v___y_4290_ = _args[22];
lean_object* v___y_4291_ = _args[23];
lean_object* v___y_4292_ = _args[24];
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4268_, v_indName_4269_, v_tail_4270_, v_params_4271_, v_is_4272_, v___x_4273_, v_head_4274_, v_ctors_4275_, v_numIndices_4276_, v___x_4277_, v___x_4278_, v_val_4279_, v_declName_4280_, v_levelParams_4281_, v_numParams_4282_, v___x_4283_, v_t_4284_, v___x_4285_, v_x1_4286_, v_x_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_x_4287_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4294_, lean_object* v_indName_4295_, lean_object* v_tail_4296_, lean_object* v_params_4297_, lean_object* v_head_4298_, lean_object* v_ctors_4299_, lean_object* v_numIndices_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v_val_4303_, lean_object* v_declName_4304_, lean_object* v_levelParams_4305_, lean_object* v_numParams_4306_, lean_object* v___x_4307_, lean_object* v_is_4308_, lean_object* v_t_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___f_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; 
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4309_);
v___f_4317_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4317_, 0, v___x_4294_);
lean_closure_set(v___f_4317_, 1, v_indName_4295_);
lean_closure_set(v___f_4317_, 2, v_tail_4296_);
lean_closure_set(v___f_4317_, 3, v_params_4297_);
lean_closure_set(v___f_4317_, 4, v_is_4308_);
lean_closure_set(v___f_4317_, 5, v___x_4315_);
lean_closure_set(v___f_4317_, 6, v_head_4298_);
lean_closure_set(v___f_4317_, 7, v_ctors_4299_);
lean_closure_set(v___f_4317_, 8, v_numIndices_4300_);
lean_closure_set(v___f_4317_, 9, v___x_4301_);
lean_closure_set(v___f_4317_, 10, v___x_4302_);
lean_closure_set(v___f_4317_, 11, v_val_4303_);
lean_closure_set(v___f_4317_, 12, v_declName_4304_);
lean_closure_set(v___f_4317_, 13, v_levelParams_4305_);
lean_closure_set(v___f_4317_, 14, v_numParams_4306_);
lean_closure_set(v___f_4317_, 15, v___x_4307_);
lean_closure_set(v___f_4317_, 16, v_t_4309_);
lean_closure_set(v___f_4317_, 17, v___x_4316_);
v___x_4318_ = 0;
v___x_4319_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4309_, v___x_4316_, v___f_4317_, v___x_4318_, v___x_4318_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4320_ = _args[0];
lean_object* v_indName_4321_ = _args[1];
lean_object* v_tail_4322_ = _args[2];
lean_object* v_params_4323_ = _args[3];
lean_object* v_head_4324_ = _args[4];
lean_object* v_ctors_4325_ = _args[5];
lean_object* v_numIndices_4326_ = _args[6];
lean_object* v___x_4327_ = _args[7];
lean_object* v___x_4328_ = _args[8];
lean_object* v_val_4329_ = _args[9];
lean_object* v_declName_4330_ = _args[10];
lean_object* v_levelParams_4331_ = _args[11];
lean_object* v_numParams_4332_ = _args[12];
lean_object* v___x_4333_ = _args[13];
lean_object* v_is_4334_ = _args[14];
lean_object* v_t_4335_ = _args[15];
lean_object* v___y_4336_ = _args[16];
lean_object* v___y_4337_ = _args[17];
lean_object* v___y_4338_ = _args[18];
lean_object* v___y_4339_ = _args[19];
lean_object* v___y_4340_ = _args[20];
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4320_, v_indName_4321_, v_tail_4322_, v_params_4323_, v_head_4324_, v_ctors_4325_, v_numIndices_4326_, v___x_4327_, v___x_4328_, v_val_4329_, v_declName_4330_, v_levelParams_4331_, v_numParams_4332_, v___x_4333_, v_is_4334_, v_t_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4342_, lean_object* v_indName_4343_, lean_object* v_tail_4344_, lean_object* v_head_4345_, lean_object* v_ctors_4346_, lean_object* v_numIndices_4347_, lean_object* v___x_4348_, lean_object* v___x_4349_, lean_object* v_val_4350_, lean_object* v_declName_4351_, lean_object* v_levelParams_4352_, lean_object* v_numParams_4353_, lean_object* v_params_4354_, lean_object* v_t_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; 
v___x_4361_ = l_Lean_Expr_bindingBody_x21(v_t_4355_);
lean_inc_ref(v___x_4361_);
lean_inc(v_numIndices_4347_);
v___f_4362_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4362_, 0, v___x_4342_);
lean_closure_set(v___f_4362_, 1, v_indName_4343_);
lean_closure_set(v___f_4362_, 2, v_tail_4344_);
lean_closure_set(v___f_4362_, 3, v_params_4354_);
lean_closure_set(v___f_4362_, 4, v_head_4345_);
lean_closure_set(v___f_4362_, 5, v_ctors_4346_);
lean_closure_set(v___f_4362_, 6, v_numIndices_4347_);
lean_closure_set(v___f_4362_, 7, v___x_4348_);
lean_closure_set(v___f_4362_, 8, v___x_4349_);
lean_closure_set(v___f_4362_, 9, v_val_4350_);
lean_closure_set(v___f_4362_, 10, v_declName_4351_);
lean_closure_set(v___f_4362_, 11, v_levelParams_4352_);
lean_closure_set(v___f_4362_, 12, v_numParams_4353_);
lean_closure_set(v___f_4362_, 13, v___x_4361_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v_numIndices_4347_);
v___x_4364_ = 0;
v___x_4365_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4361_, v___x_4363_, v___f_4362_, v___x_4364_, v___x_4364_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4366_ = _args[0];
lean_object* v_indName_4367_ = _args[1];
lean_object* v_tail_4368_ = _args[2];
lean_object* v_head_4369_ = _args[3];
lean_object* v_ctors_4370_ = _args[4];
lean_object* v_numIndices_4371_ = _args[5];
lean_object* v___x_4372_ = _args[6];
lean_object* v___x_4373_ = _args[7];
lean_object* v_val_4374_ = _args[8];
lean_object* v_declName_4375_ = _args[9];
lean_object* v_levelParams_4376_ = _args[10];
lean_object* v_numParams_4377_ = _args[11];
lean_object* v_params_4378_ = _args[12];
lean_object* v_t_4379_ = _args[13];
lean_object* v___y_4380_ = _args[14];
lean_object* v___y_4381_ = _args[15];
lean_object* v___y_4382_ = _args[16];
lean_object* v___y_4383_ = _args[17];
lean_object* v___y_4384_ = _args[18];
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4366_, v_indName_4367_, v_tail_4368_, v_head_4369_, v_ctors_4370_, v_numIndices_4371_, v___x_4372_, v___x_4373_, v_val_4374_, v_declName_4375_, v_levelParams_4376_, v_numParams_4377_, v_params_4378_, v_t_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec_ref(v_t_4379_);
return v_res_4385_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4390_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4391_ = lean_unsigned_to_nat(58u);
v___x_4392_ = lean_unsigned_to_nat(142u);
v___x_4393_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4394_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4395_ = l_mkPanicMessageWithDecl(v___x_4394_, v___x_4393_, v___x_4392_, v___x_4391_, v___x_4390_);
return v___x_4395_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4396_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4397_ = lean_unsigned_to_nat(60u);
v___x_4398_ = lean_unsigned_to_nat(136u);
v___x_4399_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4400_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4401_ = l_mkPanicMessageWithDecl(v___x_4400_, v___x_4399_, v___x_4398_, v___x_4397_, v___x_4396_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4402_, lean_object* v_indName_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4403_);
v___x_4410_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
if (lean_obj_tag(v_a_4411_) == 5)
{
lean_object* v_val_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_val_4412_ = lean_ctor_get(v_a_4411_, 0);
lean_inc_ref(v_val_4412_);
lean_dec_ref_known(v_a_4411_, 1);
v___x_4413_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4402_);
v___x_4414_ = l_Lean_Name_append(v_declName_4402_, v___x_4413_);
lean_inc(v_indName_4403_);
lean_inc(v___x_4414_);
v___x_4415_ = l_Lean_mkCasesOnSameCtorHet(v___x_4414_, v_indName_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4447_; 
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; 
v_unused_4448_ = lean_ctor_get(v___x_4415_, 0);
lean_dec(v_unused_4448_);
v___x_4417_ = v___x_4415_;
v_isShared_4418_ = v_isSharedCheck_4447_;
goto v_resetjp_4416_;
}
else
{
lean_dec(v___x_4415_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4447_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
lean_inc(v_indName_4403_);
v___x_4419_ = l_Lean_mkCasesOnName(v_indName_4403_);
v___x_4420_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4419_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v_levelParams_4422_; lean_object* v_type_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v_levelParams_4422_ = lean_ctor_get(v_a_4421_, 1);
lean_inc_n(v_levelParams_4422_, 2);
v_type_4423_ = lean_ctor_get(v_a_4421_, 2);
lean_inc_ref(v_type_4423_);
lean_dec(v_a_4421_);
v___x_4424_ = lean_box(0);
v___x_4425_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4422_, v___x_4424_);
if (lean_obj_tag(v___x_4425_) == 1)
{
lean_object* v_head_4426_; lean_object* v_tail_4427_; lean_object* v_numParams_4428_; lean_object* v_numIndices_4429_; lean_object* v_ctors_4430_; lean_object* v___f_4431_; lean_object* v___x_4433_; 
v_head_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_head_4426_);
v_tail_4427_ = lean_ctor_get(v___x_4425_, 1);
lean_inc(v_tail_4427_);
v_numParams_4428_ = lean_ctor_get(v_val_4412_, 1);
lean_inc_n(v_numParams_4428_, 2);
v_numIndices_4429_ = lean_ctor_get(v_val_4412_, 2);
lean_inc(v_numIndices_4429_);
v_ctors_4430_ = lean_ctor_get(v_val_4412_, 4);
lean_inc(v_ctors_4430_);
v___f_4431_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4431_, 0, v___x_4409_);
lean_closure_set(v___f_4431_, 1, v_indName_4403_);
lean_closure_set(v___f_4431_, 2, v_tail_4427_);
lean_closure_set(v___f_4431_, 3, v_head_4426_);
lean_closure_set(v___f_4431_, 4, v_ctors_4430_);
lean_closure_set(v___f_4431_, 5, v_numIndices_4429_);
lean_closure_set(v___f_4431_, 6, v___x_4414_);
lean_closure_set(v___f_4431_, 7, v___x_4425_);
lean_closure_set(v___f_4431_, 8, v_val_4412_);
lean_closure_set(v___f_4431_, 9, v_declName_4402_);
lean_closure_set(v___f_4431_, 10, v_levelParams_4422_);
lean_closure_set(v___f_4431_, 11, v_numParams_4428_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set_tag(v___x_4417_, 1);
lean_ctor_set(v___x_4417_, 0, v_numParams_4428_);
v___x_4433_ = v___x_4417_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_numParams_4428_);
v___x_4433_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
uint8_t v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = 0;
v___x_4435_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4423_, v___x_4433_, v___f_4431_, v___x_4434_, v___x_4434_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4435_;
}
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_dec(v___x_4425_);
lean_dec_ref(v_type_4423_);
lean_dec(v_levelParams_4422_);
lean_del_object(v___x_4417_);
lean_dec(v___x_4414_);
lean_dec_ref(v_val_4412_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v___x_4437_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4438_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_4437_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4438_;
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_del_object(v___x_4417_);
lean_dec(v___x_4414_);
lean_dec_ref(v_val_4412_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v_a_4439_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4420_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4420_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
}
else
{
lean_dec(v___x_4414_);
lean_dec_ref(v_val_4412_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
return v___x_4415_;
}
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec(v_a_4411_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v___x_4449_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4450_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_4449_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4450_;
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v_a_4451_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4410_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4410_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4459_, lean_object* v_indName_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_mkCasesOnSameCtor(v_declName_4459_, v_indName_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4467_, lean_object* v_params_4468_, lean_object* v_motive_4469_, lean_object* v_as_4470_, size_t v_sz_4471_, size_t v_i_4472_, lean_object* v_bs_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4467_, v_params_4468_, v_motive_4469_, v_sz_4471_, v_i_4472_, v_bs_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4480_, lean_object* v_params_4481_, lean_object* v_motive_4482_, lean_object* v_as_4483_, lean_object* v_sz_4484_, lean_object* v_i_4485_, lean_object* v_bs_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
size_t v_sz_boxed_4492_; size_t v_i_boxed_4493_; lean_object* v_res_4494_; 
v_sz_boxed_4492_ = lean_unbox_usize(v_sz_4484_);
lean_dec(v_sz_4484_);
v_i_boxed_4493_ = lean_unbox_usize(v_i_4485_);
lean_dec(v_i_4485_);
v_res_4494_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4480_, v_params_4481_, v_motive_4482_, v_as_4483_, v_sz_boxed_4492_, v_i_boxed_4493_, v_bs_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v_as_4483_);
lean_dec_ref(v_params_4481_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4495_, lean_object* v_params_4496_, lean_object* v_a_4497_, lean_object* v_snd_4498_, lean_object* v_alts_4499_, lean_object* v_as_4500_, size_t v_sz_4501_, size_t v_i_4502_, lean_object* v_bs_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4495_, v_params_4496_, v_a_4497_, v_snd_4498_, v_alts_4499_, v_sz_4501_, v_i_4502_, v_bs_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4510_, lean_object* v_params_4511_, lean_object* v_a_4512_, lean_object* v_snd_4513_, lean_object* v_alts_4514_, lean_object* v_as_4515_, lean_object* v_sz_4516_, lean_object* v_i_4517_, lean_object* v_bs_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
size_t v_sz_boxed_4524_; size_t v_i_boxed_4525_; lean_object* v_res_4526_; 
v_sz_boxed_4524_ = lean_unbox_usize(v_sz_4516_);
lean_dec(v_sz_4516_);
v_i_boxed_4525_ = lean_unbox_usize(v_i_4517_);
lean_dec(v_i_4517_);
v_res_4526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4510_, v_params_4511_, v_a_4512_, v_snd_4513_, v_alts_4514_, v_as_4515_, v_sz_boxed_4524_, v_i_boxed_4525_, v_bs_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec_ref(v_as_4515_);
lean_dec_ref(v_params_4511_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_4527_, lean_object* v_info_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_4527_, v_info_4528_, v___y_4530_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_4535_, lean_object* v_info_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_4535_, v_info_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4542_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
